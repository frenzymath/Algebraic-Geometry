/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartPair

/-!
# THE ATLAS IS CHART-PARAMETER HETEROGENEOUS — each chart may carry its own `n`

`Picard/Pic0ChartCoverageIndexSlack.lean` establishes that at a chart index legal at parameter
`n` the coverage theorem's threshold is forced to equal `n`, and that at `n = g` the resulting
hypothesis is false.  Both that file and the review it adjudicates (I-0660) then reason about
"the" chart parameter, as though the atlas had one.

**It does not, and this file proves it.**  `pic0RepresentableByOfCharts`
(`Picard/Pic0SigmaSheaf.lean:161`) takes a family `f : ∀ i, yoneda.obj (X i) ⟶ pic0SigmaSheaf`
indexed by an arbitrary `ι`, with `X : ι → Scheme` and a *per-index* certificate
`hf : ∀ i, IsOpenImmersion.presheaf (f i)`.  Nothing ties the `X i` together, so nothing ties
their chart parameters together either: `mixedParamChart` below builds such a family from a
per-index parameter `nn : ι → ℕ`, a per-index representation of `divFunctor C π (nn i)`, and a
per-index chart index legal *at that index's own parameter*.

## Why this matters, and it changes the shape of the residue

The `b = n` calibration is per-chart.  So the question "can coverage use DAT-0a's threshold?"
does not have to be answered uniformly: a point whose splitting field has threshold `b_L` can be
covered by *the chart whose parameter is `b_L.toNat`*, and a different point by a different
chart.  The I-0204 non-uniformity of `m` — no single exponent works for every fibre — is
therefore **not** an obstruction to the atlas; it is an argument for an atlas indexed by the
threshold, which is what a heterogeneous family is.

What this does **not** do, and the honest limit of the observation:

* it does not produce the representations.  `mixedParamChart` takes `rep i` as a hypothesis, one
  per parameter, and the divisor-representability lane supplies `divFunctor C π g` — a single
  parameter.  So the heterogeneous atlas is *admissible* but not yet *inhabited* beyond `n = g`;
* it does not discharge `IsChartUniv` at any index (still CERT-Σ-gated, `Pic0ChartPair.lean`);
* it says nothing about local surjectivity, which is DAT-B B-6 and is what would actually consume
  the freedom.

So the correct statement of the residue, refining `Pic0ChartCoverageIndexSlack`'s: **B-5's step 3
is a question about which parameters `divFunctor C π n` is representable at, not about
reconciling one parameter with one threshold.**  If representability is available only at `n = g`
then the slack must go into `Z` (and its legality is open, as recorded there); if it is available
at every `n`, coverage can be assembled chart-by-chart against each fibre's own threshold and the
`b = n` forcing is harmless.  That is a sharper question than either prior reading, and it is
addressed to the divRep lane rather than to this one.

## Main declarations

* `AlgebraicGeometry.mixedParamChart` — a chart family with a per-index chart parameter.
* `AlgebraicGeometry.isOpenImmersion_presheaf_mixedParamChart` — its `hf` clause is exactly a
  per-index `IsChartUniv`, so heterogeneity costs nothing in the certificate.
* `AlgebraicGeometry.mixedParamRepresentableBy` — such a family is admissible input to
  `pic0RepresentableByOfCharts`.  **This is the whole point**: the DAT-glue seam never sees a
  chart parameter.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {π : C.left ⟶ P1 k} [IsAffineHom π]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

variable (C π) in
/-- **A chart family whose chart parameter varies with the index.**

Each index `i` carries its own degree parameter `nn i`, its own representing object `D i` of
`divFunctor C π (nn i)`, its own twist exponent `m i` and chart index `Z i` — the latter legal
*at `nn i`*, i.e. `deg_k (Z i) = (m i)·d₁ − nn i`, which is what `chartValue_mem_pic0Subgroup`
requires for that index's chart value to land in `pic⁰`.

The construction is just `restrictChart` of `abelSigmaChart` applied pointwise; the content is
that it *typechecks*, i.e. that the target `pic0SigmaSheaf C` is parameter-free. -/
def mixedParamChart {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens) (i : ι) :
    yoneda.obj ((V i : Scheme.{u})) ⟶ (pic0SigmaSheaf C).1 :=
  restrictChart (abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)) (V i)

variable (C π) in
/-- **Heterogeneity costs nothing in the certificate**: the `hf` clause of a mixed-parameter
family is exactly a per-index `IsChartUniv`, by definition of both.

So a lane that can discharge CHART-U(c) *at one parameter* can discharge it index-by-index at
different parameters, with no additional compatibility between them — there is no coherence
condition across indices, because `pic0RepresentableByOfCharts` imposes none. -/
theorem isOpenImmersion_presheaf_mixedParamChart {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (huniv : ∀ i, IsChartUniv C π (nn i) (rep i) (m i) (Z i) (hdeg i) (V i)) (i : ι) :
    IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i) :=
  huniv i

variable (C π) in
/-- **A mixed-parameter chart family is admissible input to the DAT-glue seam.**

`pic0RepresentableByOfCharts` accepts it verbatim.  This is the statement that settles the
question `Pic0ChartCoverageIndexSlack` and I-0660 both left implicit: the representability engine
never sees a chart parameter, so the forced calibration `b = n` is a *per-chart* condition and
carries no uniformity obligation.

Note what remains hypothetical here and is not weakened by this: `hf` (i.e. `IsChartUniv`, still
CERT-Σ-gated), local surjectivity (DAT-B B-6), and the *existence* of `rep i` at parameters other
than `g` — which is the question this observation hands to the divisor-representability lane. -/
def mixedParamRepresentableBy {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (hf : ∀ i, IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))] :
    (pic0TypeFunctor C).RepresentableBy
      (Over.mk ((Scheme.LocalRepresentability.representableBy hf).homEquiv
        (𝟙 (Scheme.LocalRepresentability.glueData hf).glued)).1) :=
  pic0RepresentableByOfCharts C (mixedParamChart C π nn D rep m Z hdeg V) hf

end

end AlgebraicGeometry
