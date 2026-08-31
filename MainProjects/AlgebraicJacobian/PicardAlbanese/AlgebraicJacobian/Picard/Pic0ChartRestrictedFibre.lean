/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartUnivReduce
import AlgebraicJacobian.Picard.Pic0ChartAtlasParamFree
import AlgebraicJacobian.Picard.Pic0ChartAtlasCoupling
import AlgebraicJacobian.Picard.Pic0ChartLocusFibreGuard

/-!
# The fibre criterion at the RESTRICTED chart, and the `V`-coupling to coverage

`Picard/Pic0ChartUnivReduce.lean` reduces `IsChartUniv` — antecedent 1 of
`pic0RepresentableByOfCharts` — to `IsChartLocusFibre`.  **That reduction passes through the
unrestricted certificate, which the project's headers assert to be false**, and this file is
the repair.

## The defect, measured

`IsChartLocusFibre` (`Pic0ChartUnivReduce.lean:166`) asks for a
`ChartFibrePresented C (abelSigmaChart …) g` at every test — the datum for the *unrestricted*
chart, with `W` a free structure field.  Nothing pins `W := chartLocus`, although the docstring
there says the `W` field "is already discharged — it is `chartLocus`".  So the open `V` never
enters the hypothesis, and one term gives back the unrestricted certificate:

```
isOpenImmersion_presheaf_of_chartFibrePresented _ fun T g => (h T g).some
  : IsOpenImmersion.presheaf (abelSigmaChart …)
```

That measurement is **not** repeated here: it is landed as
`isOpenImmersion_presheaf_abelSigmaChart_of_isChartLocusFibre` and
`mono_abelSigmaChart_of_isChartLocusFibre` in `Picard/Pic0ChartLocusFibreGuard.lean`, together
with `not_isChartLocusFibre_of_not_injective` — the criterion's own emptiness guard, finally
instantiated at the Abel chart.  In `isChartUniv_of_isChartLocusFibre` the restriction to `V` is
applied *after* the unrestricted certificate is in hand, so restricting buys nothing on the way
in.

**The precise status of "false".**  `Pic0AtlasFromDivRep.lean:54`, `Pic0ChartPair.lean:14` and
`Pic0ChartOpenImmersionCriterion.lean:214` all assert that the Abel chart is not injective (the
linear system `|D|`), and by the guard above that assertion makes `IsChartLocusFibre`
unsatisfiable.  But **no declaration proves the non-injectivity**: the guard takes
`¬ Function.Injective` as a hypothesis.  So `IsChartLocusFibre` is *conditionally* unsatisfiable
— dead if the headers are right, and nobody has shown they are.  This file therefore does not
claim the old route is dead; it claims the old route is gated on a proposition the project
believes false and has never checked, which is reason enough not to build on it.

The criterion itself is **not** at fault: it is stated for an arbitrary morphism of presheaves
and is correct.  What was wrong is the *instantiation* — at `abelSigmaChart` rather than at
`restrictChart (abelSigmaChart …) V`.

## What this file provides

* `RestrictedChartFibre` — the same datum demanded at the **restricted** chart, so
  `exists_factor` only has to factor test points *of `V`*.
* `isChartUniv_of_restrictedChartFibre` — it gives `IsChartUniv` at that same `V`, one
  application of the existing criterion, with no unrestricted certificate in between.
* `necessity_of_restrictedChartFibre` — the weakening did not delete the content: the restricted
  datum still forces injectivity of the restricted chart on every test.
* `pic0RepresentableBy_of_restrictedChartFibre` — **the `V`-coupled assembly** (inbox `I-0861`):
  per-index restricted fibre data on the `hf` side, and on the coverage side the containment
  hypothesis `hV` of `Pic0ChartAtlasCoupling.liftPointwiseToOpens`, together give the
  representation.  The two sides are made to share the same `V` by typing.

## Division of labour with the two sibling files landed the same round

`Pic0ChartLocusFibreGuard.lean` records why the *old* route must not be used, and
`Pic0ChartAtlasCoupling.lean` supplies the **coverage** half of the `V`-coupling
(`liftPointwiseToOpens`, and the converse `pointwise_of_pointwise_restrictChart` showing `hV` is
exactly the gap).  This file supplies the **`hf`** half — the fibre datum at the restricted
chart — and the assembly that consumes both.  Nothing here re-proves either sibling.

## The honest limits, stated rather than left for a reviewer

* **Nothing here produces any input.**  This file replaces a badly-gated route by a
  well-gated one; it discharges no antecedent.  `rep` (divisor representability) is a hypothesis
  throughout, and `IsChartUniv` is not even statable without it.
* **`RestrictedChartFibre` at `V = ⊥` IS inhabited — settled in
  `Picard/Pic0ChartRestrictedFibreSat.lean`, and an earlier draft of this section priced it
  wrongly.**  That draft said the `sq` field needs
  `Subsingleton (pic0Subgroup C (Over.mk a₁))` over an empty base, "the triviality of `picEt`
  over the empty scheme: true, a genuinely separate lemma, and absent from the tree", and
  concluded that *no satisfiability witness exists at any `V`*.  **Both the pricing and the
  conclusion were false.**  The error was in the reduction, not the census: the `congr 1` that
  peeled the Σ-component and named `pic0Subgroup` threw away the fact that `pic0SigmaSheaf` is a
  **sheaf**, and a sheaf's value at a scheme covered by the empty sieve is terminal.  So the goal
  is closed by `Sheaf.isTerminalOfBotCover` applied to `Scheme.bot_mem_grothendieckTopology`
  (both mathlib) with no fact about `picEt` at all — `restrictedChartFibre_bot`.  The
  `exists_factor` half is free as `I-0861` measured; `sq` is free for a different and cheaper
  reason than that draft supposed.
* **Consequence, and it is the sharp form:** the class is non-empty, so the repaired route is not
  a route to an uninhabitable hypothesis, and the unmeasured-inhabitation risk that `ChartTyping`
  (`I-0779`) and `IsChartLocusFibre` carried does **not** apply here.  What that inhabitant also
  shows is that `IsChartUniv` at `V = ⊥` is free (`isChartUniv_bot`) — antecedent 1 carries no
  content in isolation — while the coverage clause is *refuted* at that same value
  (`not_coverageContainment_bot`), and at the other end `V = ⊤` the prices are swapped: coverage's
  containment becomes free and this datum returns the unrestricted certificate.  So the obligation
  is the *coupling*, and any `V` that works must be a proper intermediate open.
* **What that does NOT establish, since a draft of this file claimed it did** (`I-1012`): the two
  endpoints are **not** a non-vacuity check for the assembly below.  Two *bad* values of `V` are
  two refutations; non-vacuity of the pair needs a `V` where both clauses hold.  Inhabitation of
  the **pair** is still unmeasured at every `V`, and `necessity_of_restrictedChartFibre` is not
  that check either.  Only `RestrictedChartFibre` *alone* is now known inhabited.
* **The relation to the old form IS measured, and an earlier draft mispriced it.**  That draft
  said the transport `IsChartLocusFibre → RestrictedChartFibre` "needs the preimage `r ⁻¹ V`
  pushed forward along `W.ι`, which is real work and buys nothing".  Both halves were wrong
  (`I-0936`): it is `restrictedChartFibre_of_isChartLocusFibre` below, twelve lines, needing only
  `IsOpenImmersion.lift` — and it buys the sharp statement, because its hypothesis is exactly the
  coverage half's `hV`.  The "buys nothing" clause was the worse error: a lane holding the old
  form gets `IsChartUniv` *through the certificate three headers call false*, which is this
  file's whole premise.
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

/-! ## The datum at the restricted chart -/

variable (C π n) in
/-- **The fibre datum demanded at the restricted chart** — the repair of `IsChartLocusFibre`.

Identical to `IsChartLocusFibre` except that the presented morphism is
`restrictChart (abelSigmaChart …) V` rather than `abelSigmaChart …`.  The difference is the
whole point: `exists_factor` now only factors test points *of `V`*, so proving it does not
entail that the unrestricted Abel chart is a monomorphism.

`V` is a parameter and no choice is privileged here; the intended instantiation is the chart
locus, whose openness is CHART-U(b) and a separate obligation. -/
def RestrictedChartFibre {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) : Prop :=
  ∀ (T : Scheme.{u}) (g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1),
    Nonempty (ChartFibrePresented C
      (restrictChart (abelSigmaChart C π n rep m Z hdeg) V) g)

/-- **The repaired reduction**: the restricted datum gives `IsChartUniv` at the same `V`.

One application of the existing criterion, at the restricted chart.  Compare
`isChartUniv_of_isChartLocusFibre`, which applies it at the unrestricted chart and composes
afterwards — and therefore needs the unrestricted certificate on the way in. -/
theorem isChartUniv_of_restrictedChartFibre {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (h : RestrictedChartFibre C π n rep m Z hdeg V) :
    IsChartUniv C π n rep m Z hdeg V :=
  isOpenImmersion_presheaf_of_chartFibrePresented _ fun T g => (h T g).some

/-- The restricted datum forces the restricted chart to be injective on every test.

**This is NOT a non-vacuity check, and an earlier draft of this file claimed it was**
(`I-0937`).  Two reasons it does not carry that weight: its conclusion is *free* at `V = ⊥` with
no hypothesis at all (a test point of the empty open forces the test empty, hence initial); and
at general `V` it is `injective_of_isChartUniv` (`Pic0ChartUnivReduce.lean:205`) composed with
`isChartUniv_of_restrictedChartFibre`, i.e. a property of *any* hypothesis implying `IsChartUniv`,
not evidence about this one.

The real non-vacuity statement for the assembly is the pair `isChartUniv_bot` /
`not_coverageContainment_bot` in `Picard/Pic0ChartRestrictedFibreSat.lean`: `⊥` is where this
side is free and the coverage side is impossible, so the two hypotheses cannot both be met at a
convenient `V`.

Kept because it is the right thing to cite when asking what a producer of the datum must
establish — the relative form of DAT-C GAP-2, over `V` rather than over `D.left`. -/
theorem necessity_of_restrictedChartFibre {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (h : RestrictedChartFibre C π n rep m Z hdeg V)
    (T : Scheme.{u}ᵒᵖ) :
    Function.Injective
      ((restrictChart (abelSigmaChart C π n rep m Z hdeg) V).app T) :=
  injective_of_chartFibrePresented _ (fun T' g => (h T' g).some) T

/-! ## The transport, and what it says about the two halves of the coupling

An earlier draft of this file priced this transport as "real work needing a pushforward" and
declined to prove it.  **That was wrong** (inbox `I-0936`): no preimage and no pushforward are
involved — keep the old datum's `W` and lift its `r` along `V.ι`. -/

/-- **`IsChartLocusFibre` plus a range containment gives `RestrictedChartFibre`.**

And the containment is the *same* one the coverage half owes: `hr` here is character-for-character
the `hV` of `Pic0ChartAtlasCoupling.liftPointwiseToOpens`, asked on the fibre side instead of the
coverage side.  So the two halves of the `V`-coupling are **not two obligations** — they are one
range containment asked twice, from opposite directions.

This is the sharp form of "the restricted datum is weaker", and it is what makes the repair
precise rather than merely differently-shaped. -/
theorem restrictedChartFibre_of_isChartLocusFibre {D : Over (Spec (.of k))}
    (rep : (divFunctor C π n).RepresentableBy D)
    (m : ℕ) (Z : (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : Scheme.CurveDivisor.deg k Z
      = (m : ℤ) * classDeg k (thetaCechClass C) - (n : ℤ))
    (V : D.left.Opens) (h : IsChartLocusFibre C π n rep m Z hdeg)
    (hr : ∀ (T : Scheme.{u}) (g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1),
      Set.range (((h T g).some.r).base) ⊆ Set.range ((V.ι).base)) :
    RestrictedChartFibre C π n rep m Z hdeg V := by
  intro T g
  refine ⟨⟨(h T g).some.W, IsOpenImmersion.lift V.ι ((h T g).some.r) (hr T g), ?_, ?_⟩⟩
  · rw [restrictChart, ← Category.assoc, ← yoneda.map_comp, IsOpenImmersion.lift_fac]
    exact (h T g).some.sq
  · intro S v w hvw
    obtain ⟨u, hu1, hu2⟩ := (h T g).some.exists_factor S (v ≫ V.ι) w (by
      rw [← hvw, restrictChart]
      rfl)
    exact ⟨u, (cancel_mono V.ι).mp (by rw [Category.assoc, IsOpenImmersion.lift_fac]; exact hu1),
      hu2⟩

/-! ## The `V`-coupled assembly -/

variable (C π) in
/-- The `hf` clause of a mixed-parameter atlas, from per-index restricted fibre data.

Named because the representing object of the assembly below mentions it. -/
theorem mixedParamHf {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (huniv : ∀ i, RestrictedChartFibre C π (nn i) (rep i) (m i) (Z i) (hdeg i) (V i))
    (i : ι) :
    IsOpenImmersion.presheaf (mixedParamChart C π nn D rep m Z hdeg V i) :=
  isChartUniv_of_restrictedChartFibre (rep i) (m i) (Z i) (hdeg i) (V i) (huniv i)

variable (C π) in
/-- **THE `V`-COUPLED ASSEMBLY** — the composition inbox `I-0861` names as missing.

Antecedents 1 and 2 of `pic0RepresentableByOfCharts` are *not* independent.  Coverage produces a
point `x : (W : Scheme) ⟶ X i` of the chart **source**, which for the real atlas is
`(V i : Scheme)` — so coverage has to reach the very `V i` at which `hf` was certified, and no
statement in the tree said so.  Here they are forced to share `V` by typing: `huniv` certifies
the charts at `V`, and `hcov`'s witness lands in the same `V i`.

**This closes no gate.**  `rep`, `huniv` and `hcov` are all hypotheses and none has a producer.
What the statement buys is that a lane discharging `hf` and a lane discharging coverage can no
longer each succeed at a *different* `V` and report the pair as composed. -/
def pic0RepresentableBy_of_restrictedChartFibre {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (huniv : ∀ i, RestrictedChartFibre C π (nn i) (rep i) (m i) (Z i) (hdeg i) (V i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V))] :
    (pic0TypeFunctor C).RepresentableBy
      (Over.mk ((Scheme.LocalRepresentability.representableBy
        (mixedParamHf C π nn D rep m Z hdeg V huniv)).homEquiv
        (𝟙 (Scheme.LocalRepresentability.glueData
          (mixedParamHf C π nn D rep m Z hdeg V huniv)).glued)).1) :=
  pic0RepresentableByOfCharts C (mixedParamChart C π nn D rep m Z hdeg V)
    (mixedParamHf C π nn D rep m Z hdeg V huniv)

variable (C π) in
/-- **The same assembly with the local-surjectivity instance produced from coverage data**, so
that the shared `V` is visible in the hypotheses rather than hidden in an instance binder.

The instance version above states the seam at the named representing object (which is what the
`JacobianData` layer consumes); this version is the one a *coverage* lane reads, because both of
its geometric hypotheses mention the same `V i`: `huniv` certifies the charts there, and `hcov`'s
range containment — `Pic0ChartAtlasCoupling`'s `hV` — puts the coverage witness there.

The conclusion is stated as a `Σ` only because the named object above mentions the instance this
definition constructs; the representing scheme is the same one. -/
def pic0RepresentableBy_of_restrictedChartFibre_of_coverage {ι : Type u} (nn : ι → ℕ)
    (D : ι → Over (Spec (.of k)))
    (rep : ∀ i, (divFunctor C π (nn i)).RepresentableBy (D i))
    (m : ι → ℕ) (Z : ι → (C ⊗ overSpec k k).left.CurveDivisor)
    (hdeg : ∀ i, Scheme.CurveDivisor.deg k (Z i)
      = (m i : ℤ) * classDeg k (thetaCechClass C) - (nn i : ℤ))
    (V : ∀ i, (D i).left.Opens)
    (huniv : ∀ i, RestrictedChartFibre C π (nn i) (rep i) (m i) (Z i) (hdeg i) (V i))
    (hcov : ∀ (T : Scheme.{u}) (s : (pic0SigmaSheaf C).1.obj (op T)) (t : ↥T),
      ∃ (W : T.Opens) (_ : t ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ (D i).left),
        (abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)).app
            (op (W : Scheme.{u})) x
          = (pic0SigmaSheaf C).1.map (W.ι).op s ∧
        Set.range (x.base) ⊆ Set.range ((V i).ι.base)) :
    Σ J : Over (Spec (.of k)), (pic0TypeFunctor C).RepresentableBy J :=
  letI : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (mixedParamChart C π nn D rep m Z hdeg V)) :=
    isLocallySurjective_restrictChart_of_pointwise C
      (fun i => abelSigmaChart C π (nn i) (rep i) (m i) (Z i) (hdeg i)) V hcov
  ⟨_, pic0RepresentableBy_of_restrictedChartFibre C π nn D rep m Z hdeg V huniv⟩

end

end AlgebraicGeometry
