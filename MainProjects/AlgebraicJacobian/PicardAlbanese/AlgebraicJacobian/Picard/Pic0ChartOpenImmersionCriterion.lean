/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartPair

/-!
# C9b: what `IsOpenImmersion.presheaf` of a chart map actually asks for

`Picard/Pic0ChartPair.lean` pins `IsChartUniv` — the `hf` half of the `(f, hf)` pair that
`pic0RepresentableByOfCharts` consumes — and its docstring, together with the `c9b` roadmap
row, prices it as **one** obligation: the relative form of DAT-C GAP-2 plus the classifier,
CERT-Σ-gated.

**That pricing is wrong, and this file is the correction.**  `IsOpenImmersion.presheaf` is
`MorphismProperty.relative` at `yoneda` (mathlib `MorphismProperty/Representable.lean`), and
`relative` is *by definition* a conjunction of two independent statements:

1. **relative representability** — for every test `T` and every `g : yoneda.obj T ⟶ 𝓟`, the
   fibre product of the chart map along `g` is representable *by a scheme*;
2. **the property clause** — every represented pullback is an open immersion of schemes.

The GAP-2/classifier story is the input to (2) only: it is what makes the fibre a single
point, hence the represented pullback an open subscheme.  It says nothing about (1), which
is a representability statement about a fibre product.  Read as one clause, a lane waits on
CERT-Σ for both halves.  Read as two, half of the work is stateable and provable *now*, with
no divisor-representability endpoint and no certificate anywhere in it.

## What this file provides, and what it deliberately does not

Everything here is stated for an **arbitrary** morphism of big-site presheaves
`f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1` and an **arbitrary** open `V ⊆ X`.  No `divRep`
endpoint, no certificate, no `Z`, no `θ` and no chart index appears in any statement.  That
is the point: `IsChartUniv` becomes *this criterion instantiated at* `abelSigmaChart`, and
the divisor-representability shape enters only at the instantiation.

The criterion's hypotheses are **elementwise** conditions on the presheaf — a fibrewise
injectivity clause and a clause producing the representing open — because that is what
mathlib's `MorphismProperty.relative.of_exists` reduces the goal to once the presheaf
category's pullbacks are computed pointwise (`Types.isPullback_iff`).

## Main declarations

* `AlgebraicGeometry.ChartFibrePresented` — the elementwise datum (1) needs: for each test
  point `g` of the target, an open `W` of the test and an identification of the `W`-points
  with the chart points hitting `g`.  This is the *shape* of a fibre-product presentation,
  named so that a producer knows exactly what it owes.
* `AlgebraicGeometry.isOpenImmersion_presheaf_of_chartFibrePresented` — **the criterion**:
  a `ChartFibrePresented` datum gives `IsOpenImmersion.presheaf f`, discharging BOTH clauses
  at once.  Certificate-free and divRep-free.
* `AlgebraicGeometry.mono_of_isOpenImmersion_presheaf` — the converse direction that makes
  the split honest: `IsOpenImmersion.presheaf f` *implies* `f` is a monomorphism.  So "the
  Abel map is not a monomorphism", which three files cite as the reason the unrestricted
  certificate fails, is a consequence of the criterion rather than an extra obligation — and
  it shows the elementwise injectivity clause below is **necessary**, not an artefact of
  this route.
* `AlgebraicGeometry.injective_of_isOpenImmersion_presheaf` — the same fact in the
  elementwise form a chart-locus argument can actually use.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The necessary direction: an open immersion of presheaves is a monomorphism

Stated first, because it is what tells us the criterion below asks for the right thing. -/

/-- **An open immersion of presheaves out of a representable is a monomorphism.**

This is mathlib's `presheaf_mono_of_le` at `P := IsOpenImmersion`, whose hypothesis
`IsOpenImmersion ≤ monomorphisms Scheme` is the landed `IsOpenImmersion.le_monomorphisms`.

Recorded because the whole chart layer rests on the sentence "the Abel map is not a
monomorphism, so `IsOpenImmersion.presheaf` is false for the unrestricted divisor scheme"
(`Pic0AtlasFromDivRep.lean:54`, repeated in `Pic0ChartPair.lean:14`).  That sentence is a
*derivation*, not an independent input, and this lemma is the derivation. -/
theorem mono_of_isOpenImmersion_presheaf {X : Scheme.{u}}
    {f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1} (hf : IsOpenImmersion.presheaf f) :
    Mono f :=
  MorphismProperty.presheaf_mono_of_le IsOpenImmersion.le_monomorphisms hf

/-- **The elementwise form of the necessary direction**: if `f` is an open immersion of
presheaves then on every test it is injective on points.

This is the clause `ChartFibrePresented.fibre_injective` below, read backwards, and it is
why that clause is not an artefact of this particular route: any proof of
`IsOpenImmersion.presheaf f` whatsoever yields it.  For the Abel chart it is exactly "the
normalized effective representative is unique", i.e. the relative form of DAT-C GAP-2 — so
GAP-2 is *forced* by the target, not merely sufficient for it. -/
theorem injective_of_isOpenImmersion_presheaf {X : Scheme.{u}}
    {f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1} (hf : IsOpenImmersion.presheaf f)
    (T : Scheme.{u}ᵒᵖ) :
    Function.Injective (f.app T) :=
  (mono_iff_injective (f.app T)).mp
    ((NatTrans.mono_iff_mono_app f).mp (mono_of_isOpenImmersion_presheaf hf) T)

/-! ## The sufficient direction: the elementwise datum, and the criterion -/

variable (C) in
/-- **The fibre of a chart map over one test point, presented by an open of the test.**

This is the datum mathlib's `relative.of_exists` asks for at a single
`g : yoneda.obj T ⟶ pic0SigmaSheaf C`, written out so a producer can see exactly what it
owes.  Given a chart map `f` out of `X`:

* `W` is an open subscheme of the test `T` — the locus where the class named by `g` *is* a
  chart value.  For the Abel chart this is `chartLocus`;
* `r` recovers the chart point: over `W`, the divisor family whose class `g` is;
* `sq` says the two ways round agree;
* `exists_factor` is the honest content — a test point of `X` and a test point of `T` with
  the *same* class come from a unique point of `W`.  Existence is coverage-on-the-locus;
  the uniqueness half is *not* a field here, because it is free: `W.ι` is a monomorphism.

Nothing in this structure mentions a divisor scheme, a certificate, a twist or a chart
index.  It is a statement about a morphism of presheaves and an open of a test. -/
structure ChartFibrePresented {X T : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1)
    where
  /-- The locus of the test where the class named by `g` is a chart value. -/
  W : T.Opens
  /-- The chart point over that locus. -/
  r : (W : Scheme.{u}) ⟶ X
  /-- The square commutes: `r` names the class `g` restricted to `W`. -/
  sq : yoneda.map r ≫ f = yoneda.map W.ι ≫ g
  /-- **Coverage on the locus**: an `S`-point of `X` and an `S`-point of `T` carrying the
  same class factor through `W`, compatibly with both projections. -/
  exists_factor : ∀ (S : Scheme.{u}) (v : S ⟶ X) (w : S ⟶ T),
    f.app (op S) v = g.app (op S) w → ∃ u : S ⟶ (W : Scheme.{u}), u ≫ r = v ∧ u ≫ W.ι = w

namespace ChartFibrePresented

variable {X T : Scheme.{u}} {f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1}
  {g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1}

/-- **The datum presents the fibre product**: the square of `ChartFibrePresented` is a
pullback of presheaves.

Pullbacks in a presheaf category are computed pointwise
(`IsPullback.of_forall_isPullback_app`), and a pointwise pullback of types is exactly
"commutes + jointly injective + jointly surjective" (`Types.isPullback_iff`).  The first is
`sq`, the third is `exists_factor`, and the second is free from `W.ι` being a
monomorphism — which is where the openness of `W` does its work. -/
theorem isPullback (D : ChartFibrePresented C f g) :
    IsPullback (yoneda.map D.r) (yoneda.map D.W.ι) f g := by
  refine IsPullback.of_forall_isPullback_app fun S => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun φ : yoneda.obj (D.W : Scheme.{u}) ⟶ (pic0SigmaSheaf C).1 =>
      φ.app S) D.sq
  · -- joint injectivity: already forced by `W.ι` alone, being a monomorphism
    rintro u₁ u₂ ⟨-, h₂⟩
    have : u₁ ≫ D.W.ι = u₂ ≫ D.W.ι := h₂
    exact (cancel_mono D.W.ι).mp this
  · -- joint surjectivity: `exists_factor` at the test `S.unop`
    intro v w hvw
    obtain ⟨u, hu₁, hu₂⟩ := D.exists_factor S.unop v w hvw
    exact ⟨u, hu₁, hu₂⟩

end ChartFibrePresented

/-- **THE CRITERION** — `IsOpenImmersion.presheaf` from elementwise data, discharging BOTH
clauses of `MorphismProperty.relative` at once.

Given, for every test point of the target sheaf, a `ChartFibrePresented` datum, the chart map
is an open immersion of presheaves.  Certificate-free, divRep-free, and with no reference to
divisors: the input is a family of opens of tests together with the coverage statement on
each.

This is the honest shape of `IsChartUniv`'s obligation.  Reading `IsOpenImmersion.presheaf`
as a single "relative GAP-2" statement conflates:

* **relative representability** — that the fibre product is a scheme at all.  Supplied here
  by `W`, an open subscheme of the test, and proved by `ChartFibrePresented.isPullback`;
* **the property clause** — that each represented pullback is an open immersion.  Supplied
  here by `W.ι` being an open immersion, which is free.

What is *not* free, and is the whole mathematical content, is `exists_factor`: a class that
agrees with a chart value must come from the locus.  For the Abel chart that is the relative
form of DAT-C GAP-2 (uniqueness of the normalized effective representative) fed through the
classifier — so the CERT-Σ gate is real, but it gates ONE field of ONE structure rather than
the whole certificate. -/
theorem isOpenImmersion_presheaf_of_chartFibrePresented {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (D : ∀ (T : Scheme.{u}) (g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1),
      ChartFibrePresented C f g) :
    IsOpenImmersion.presheaf f := by
  refine MorphismProperty.relative.of_exists fun T g => ?_
  exact ⟨(D T g).W, yoneda.map (D T g).r, (D T g).W.ι, (D T g).isPullback,
    inferInstance⟩

/-! ## The criterion is not vacuous

A structure whose hard field is an existential can be inhabited for trivial reasons, and a
criterion built on one is then worthless.  This section rules that out **by proof** rather
than by inspection: the datum is unconstructible exactly when it must be. -/

/-- **Non-vacuity of `ChartFibrePresented`, from the necessary direction.**

If a chart map fails to be injective on the points of even one test, then no family of
`ChartFibrePresented` data exists for it.  In particular the criterion cannot be satisfied
for the *unrestricted* Abel chart, whose non-injectivity is the linear system `|D|`
(`Pic0AtlasFromDivRep.lean:54`): the criterion's hypothesis is genuinely as strong as the
conclusion, and `exists_factor` is not a clause one can talk one's way past.

The proof composes the two halves of this file, which is the point of having both. -/
theorem isEmpty_forall_chartFibrePresented_of_not_injective {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1) (T : Scheme.{u}ᵒᵖ)
    (hT : ¬ Function.Injective (f.app T)) :
    IsEmpty (∀ (T' : Scheme.{u}) (g : yoneda.obj T' ⟶ (pic0SigmaSheaf C).1),
        ChartFibrePresented C f g) :=
  ⟨fun D => hT (injective_of_isOpenImmersion_presheaf
    (isOpenImmersion_presheaf_of_chartFibrePresented f D) T)⟩

/-- The same statement in the form a lane will meet it: the criterion's input **implies**
elementwise injectivity on every test.  So a lane that cannot prove uniqueness of the
normalized effective representative cannot supply the datum either — the CERT-Σ gate is not
an artefact of how `IsChartUniv` was pinned. -/
theorem injective_of_chartFibrePresented {X : Scheme.{u}}
    (f : yoneda.obj X ⟶ (pic0SigmaSheaf C).1)
    (D : ∀ (T : Scheme.{u}) (g : yoneda.obj T ⟶ (pic0SigmaSheaf C).1),
      ChartFibrePresented C f g) (T : Scheme.{u}ᵒᵖ) :
    Function.Injective (f.app T) :=
  injective_of_isOpenImmersion_presheaf
    (isOpenImmersion_presheaf_of_chartFibrePresented f D) T

end

end AlgebraicGeometry
