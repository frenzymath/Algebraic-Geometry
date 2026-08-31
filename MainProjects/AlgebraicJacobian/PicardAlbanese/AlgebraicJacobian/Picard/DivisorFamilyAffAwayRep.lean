/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffGlueZarKit

/-!
# STEP 1 OF THE CLASSIFIER, WIDENED: a widened class has certified away representatives

Roadmap leaf `AJCR.w4-rep.datum.dat-d.ddr.certificate.cert-assemble`; the *classifier* direction.

`…AffSeedGate.lean` / `…AffSeedSection.lean` gave the widened carrier a producer from geometry, so
`divFunctorAff` now receives values.  The other half of `DivRepGlobalData` is the **classifier**
`divRepClassifyZar` (`DivRepClassifyZar.lean:244`), and its route begins with

  `DivFamZar.exists_certified_away_rep`  (`DivRepClassifyZarKit.lean:79`)

— step 1 of the ddr9 worksheet: a locally certified class restricts, on a finite span-`⊤` family
of basic opens of the base, to *classes of certified families* over the away localizations.

This file is that theorem at `DivFamZarAff`.

## Why this port is legitimate, and why it is the RIGHT next brick

`…AffFraming.lean` already scoped what a widened classifier needs, and correctly identified that
`DivFamZar.exists_certChartCover` — step 1 **plus** the ε-framing — does not port wholesale,
because its proof runs through the two-chart `PairChartRing` window.  That remains true, and this
file does not claim otherwise.

What this file observes is that step 1 **by itself** contains no chart content whatsoever.  Read
the chart-typed proof: it takes a `Quotient` representative, reads the `IsLocallyCertified`
existential the subtype carries, and repackages the recorded `DivEq` as a `mk`-equality.  Every
step is about the quotient and the base-side away family; `π` appears only in the *type* of the
carrier, never in an argument.  So the widened statement is provable by the same four moves at
`DivFamZarAff`, and the two places the spellings differ are exactly the two ADDENDUM 9 §9.2 warns
about: the widened `mapAlg` needs `[IsProper C.hom]` for its overlap-affineness, and the certified
family's own local certifiability is `CertifiedDivisorFamilyAff.isLocallyCertifiedAff` rather than
`(DivFam.mk G).toZar`.

**What is still owed for a widened classifier** — stated so this file is not read as more than it
is: the ε-framing half of `exists_certChartCover`.  Its inputs exist on the widened side
(`CertifiedDivisorFamilyAff.eps`, `.IsPairChartFramed`, `…AffFraming.lean`); what does not exist is
the derivation that the framing can be *achieved* over each away piece, and that derivation is
genuinely two-chart.  This file supplies its first input and no more.

## Main declarations

* `AlgebraicGeometry.DivFamZarAff.exists_certified_away_rep` — step 1, widened.
* `AlgebraicGeometry.DivFamZarAff.exists_certified_away_rep_of_mk` — the same read at a `mk`, for a
  caller holding the system rather than the class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))} [IsProper C.hom]
variable {S : Type u} [CommRing S] [Algebra k S] {n : ℕ}

/-- **Step 1 of the classifier, at the widened carrier.**  A widened locally certified class over
`S` restricts, on a finite span-`⊤` family of basic opens, to the classes of *widened* certified
divisor families over the canonical away localizations.

The chart-typed twin is `DivFamZar.exists_certified_away_rep` (`DivRepClassifyZarKit.lean:79`), and
the proof is the same four moves — take a quotient representative, read the pin's existential,
recover the recorded `DivEq`, repackage as a `mk`-equality.  No step mentions a chart, a partition,
or `π`: step 1 is entirely about the quotient and the Zariski cover of the BASE, which R2 did not
touch.

`[IsProper C.hom]` is carried because the widened `mapAlg` needs it (ADDENDUM 6 item 3: an
arbitrary affine open's overlaps are not affine by fiat), and it is a hypothesis the DD-R lane has
everywhere. -/
theorem DivFamZarAff.exists_certified_away_rep (F₀ : DivFamZarAff C S n) :
    ∃ (m : ℕ) (h : Fin m → S), Ideal.span (Set.range h) = ⊤ ∧
      ∀ l : Fin m, ∃ G : CertifiedDivisorFamilyAff C (Localization.Away (h l)) n,
        G.toZarAff = DivFamZarAff.mapAlg (Localization.Away (h l)) n F₀ := by
  obtain ⟨dp, hdp⟩ := Quotient.exists_rep F₀
  obtain ⟨m, h, hspan, hG⟩ := dp.2
  refine ⟨m, h, hspan, fun l => ?_⟩
  haveI : IsOpenImmersion (relCurveMap C S (Localization.Away (h l))) :=
    isOpenImmersion_relCurveMap_away C S (Localization.Away (h l)) (h l)
  obtain ⟨G, hGdiv⟩ := hG l
  refine ⟨G, ?_⟩
  rw [← hdp]
  exact DivFamZarAff.mk_eq_mk_iff.mpr hGdiv

/-- Step 1 read at an explicit system and pin, for a caller who has just produced one (e.g. from
`ThetaGeneratorSeed.isLocallyCertifiedAff_of_swallowing_affineOpen`) and has not packaged the
class yet. -/
theorem DivFamZarAff.exists_certified_away_rep_of_mk
    {d : (relCurve C S).LocalEquations} (hd : IsLocallyCertifiedAff n d) :
    ∃ (m : ℕ) (h : Fin m → S), Ideal.span (Set.range h) = ⊤ ∧
      ∀ l : Fin m, ∃ G : CertifiedDivisorFamilyAff C (Localization.Away (h l)) n,
        G.toZarAff = DivFamZarAff.mapAlg (Localization.Away (h l)) n
          (DivFamZarAff.mk d hd) :=
  DivFamZarAff.exists_certified_away_rep _

end AlgebraicGeometry
