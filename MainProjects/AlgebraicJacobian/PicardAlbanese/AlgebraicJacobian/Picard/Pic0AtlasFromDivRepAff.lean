/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffClassDegree
import AlgebraicJacobian.Picard.Pic0SigmaSheaf

/-!
# The Σ-chart over the R2 carrier: the widened Abel chart reaches the seam

`Picard/DivisorFamilyAffClassDegree.lean` discharges `hdegAff`, so the widened chart value is
a degree-zero class with no hypothesis beyond the chart-index constraint.  **This file spends
that**: the widened analogues of `chartValueTrans` and `abelSigmaChart`
(`Picard/Pic0AtlasFromDivRep.lean:174/205`), which take the R2 carrier mandated by human
decision `I-0492` all the way to the input type of `pic0RepresentableByOfCharts`.

## What this closes, and it is a carrier-target gap rather than a lemma

Memory `census-the-carrier-target-pair` records the defect this repairs: a replaced carrier can
be fully built — quotient, base change, functoriality, gluing, a functor `divFunctorAff`, a
comparison `divFunctorToAff`, a Picard class with naturalities — and still reach *no* consumer,
because the arrow into the category the consumer's signature names is what nobody opens a row
for.  `ajcr-p3` closed the Abel-value half of that gap (`Picard/DivisorFamilyAffAbel.lean`);
what remained was the *degree ledger*, and with it discharged the two arrows below are the
chart-typed definitions verbatim, with `divFunctorAff` in place of `divFunctor`.

So the answer to "does the human's carrier reach the representability seam?" is now **yes, as
Lean rather than as prose**: `abelSigmaChartAff` has exactly the type `pic0RepresentableByOfCharts`
consumes for its `f i`.

## What is still open, stated precisely

`rep` — here `(divFunctorAff C n).RepresentableBy D` — is a **hypothesis**, exactly as in the
chart-typed `abelSigmaChart`, and **nothing in the tree produces one**.  So this file supplies a
chart *shape*, not a chart.  Both antecedents of the seam remain untouched:

* `IsChartUniv` for this family (antecedent 1) is not stated here, let alone proved;
* Zariski-local surjectivity of `Sigma.desc` (antecedent 2) is untouched, and by
  `isLocallySurjective_unrestricted` (`Picard/Pic0ChartVMonotone.lean`) restricting to any open
  does not weaken it.

What changes is *which* divisor-representability statement the campaign may aim at: a producer
of `(divFunctorAff C n).RepresentableBy` now suffices, and the R2 widening exists precisely
because that one may be reachable where the chart-typed one is blocked by the `(c1)` no-go
(`Picard/DivSchemeCertZarC1.lean:131`; the separation is
`isCertified_affine_and_not_isCertified_chart`, `Picard/DivisorFamilyAffStrict.lean`, whose own
scope note records that the separating divisor is *not* exhibited in this tree).  That is a
re-aiming of the target, not a discharge of it.

## Main declarations

* `AlgebraicGeometry.chartValueAffTrans` — the widened `chartValueTrans`: a natural
  transformation `divFunctorAff C n ⟶ pic0TypeFunctor C`.
* `AlgebraicGeometry.abelSigmaChartAff` — the widened Abel chart map, of exactly the type
  `pic0RepresentableByOfCharts` accepts.
* `AlgebraicGeometry.chartHom_abelSigmaChartAff` — its chart structure morphism is `D.hom`, so
  the seam's finiteness certificates read off the representing object as before.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] Over.sectionsAlgebra Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom] {n : ℕ}
variable [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
variable [GeometricallyReduced C.hom]

noncomputable section

variable (C n) in
/-- **The widened Abel transformation into the degree-zero Picard functor** — the R2 analogue of
`chartValueTrans` (`Picard/Pic0AtlasFromDivRep.lean:174`).

The degree ledger that makes the target the degree-*zero* functor is
`chartValueAff_mem_pic0Subgroup'`, i.e. `hdegAff` discharged
(`Picard/DivisorFamilyAffClassDegree.lean`); naturality is `picEtMap_chartValueAff`.  Neither
step mentions a chart, a partition of unity or a pinned pair — and note there is no `π` in the
signature at all, the widened carrier being `π`-free. -/
def chartValueAffTrans (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    divFunctorAff C n ⟶ pic0TypeFunctor C where
  app T := TypeCat.ofHom fun s => ⟨chartValueAff C n m Z T.unop s,
    chartValueAff_mem_pic0Subgroup' m Z hdeg T.unop s⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    exact Subtype.ext ((picEtMap_chartValueAff C n m Z g.unop s).symm)

@[simp]
lemma chartValueAffTrans_app_coe (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (T : (Over (Spec (.of k)))ᵒᵖ) (s : divFamZarAff C n T.unop) :
    ((chartValueAffTrans C n m Z hdeg).app T s).1 = chartValueAff C n m Z T.unop s :=
  rfl

variable (C n) in
/-- **The widened Abel chart map** — the R2 analogue of `abelSigmaChart`
(`Picard/Pic0AtlasFromDivRep.lean:205`), and the point of this file: it has exactly the type
`pic0RepresentableByOfCharts` (`Picard/Pic0SigmaSheaf.lean:161`) consumes for its `f i`.

`rep` is a **hypothesis**, verbatim as in the chart-typed original, and nothing in the tree
produces a representation of `divFunctorAff` any more than of `divFunctor`.  What this def
establishes is that the carrier `I-0492` mandates is admissible input to the seam — a
carrier-target arrow, not a discharge. -/
def abelSigmaChartAff {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ)) :
    yoneda.obj D.left ⟶ (pic0SigmaSheaf C).1 :=
  rep.toSigmaExtension ≫ Over.sigmaExtensionNat (chartValueAffTrans C n m Z hdeg)

/-- **The structure morphism of the widened Abel chart is that of the representing object** —
verbatim `chartHom_abelSigmaChart`.  So the seam's finiteness hypotheses specialise to
`LocallyOfFiniteType D.hom` and `CompactSpace D.left`, properties of the widened divisor scheme
with no reference to the Picard functor, exactly as on the chart-typed side. -/
lemma chartHom_abelSigmaChartAff {D : Over (Spec (.of k))}
    (rep : (divFunctorAff C n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    {ι : Type u} (i : ι) :
    chartHom C (fun _ : ι => abelSigmaChartAff C n rep m Z hdeg) i = D.hom :=
  Category.id_comp _

end

end AlgebraicGeometry
