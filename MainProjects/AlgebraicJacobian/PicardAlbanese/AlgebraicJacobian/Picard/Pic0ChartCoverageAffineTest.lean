/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartCoveragePointwise

/-!
# DAT-B B-5: the coverage obligation is Zariski-local in the test, so AFFINE tests suffice

`Picard/Pic0ChartCoveragePointwise.lean` reduced `ChartsCoverLocally` — and with it
antecedent 2 of `pic0RepresentableByOfCharts` — to pointwise data at **every test scheme
`T`**.  That is where the reduction chain stops, and the quantifier it stops at is the
problem this file addresses.

**Every divisor-side producer in this project is indexed by a RING, not by a scheme.**
`DivFamZar C S π n` (`Picard/DivisorFamilyZar.lean:235`) is a quotient of local-equation
systems over an algebra `S`; `divFamZar C π n T` at a general test
(`Picard/DivisorFamilyZarVehicle.lean:187`) is the affine-opens *limit* of those, and the
comparison `divFamZarAffineEquiv` (:300) collapses it to `DivFamZar` only on an affine
test.  Likewise every producer of a certified family, of an effective witness
(`DivisorFamilyFieldSurj.lean:147`), and every classifier
(`effectiveDivisorClassifyZar`, :217) is stated over a ring or a field.  So a coverage
lane facing "for every scheme `T`" has to cross the affine-to-general gap **before** it can
use any of that machinery, and nothing said it was allowed to skip it.

It is allowed to skip it, and that is this file's content.

## Why locality in the test is not bookkeeping the producer can inline

The naive argument — "sieves are local, so restrict to an affine cover" — is not available
as stated, because `ChartsCoverLocally` is a statement about the sieve on `T` itself, and
the pointwise hypothesis quantifies over points of `T`.  Three things have to be checked,
and each is where the argument could fail:

* **the class must restrict.**  The datum at a point `t` of an affine piece `Y` is about a
  section over an open of `Y`, while the obligation at `t : ↥T` is about an open of `T`.
  Composing `W.ι ≫ 𝒰.f j` gives a map into `T` but not an *open of* `T`, so the transport
  cannot be done at the level of `T.Opens` — it has to be done at the level of the sieve,
  where an arbitrary morphism is allowed;
* **the sieve must be transitive.**  Membership of `⨆ i, imageSieve (f i) s` in the
  topology on `T` is deduced from membership of its *pullbacks* along the cover maps, which
  is `GrothendieckTopology.transitive` plus `Presheaf.pullback_imageSieve` — the latter is
  what says the pullback of an image sieve is the image sieve of the restricted section,
  i.e. that the obligation at `Y` is about `s|_Y` and nothing else;
* **the pullback must commute with the supremum.**  `Sieve.pullback` is a left adjoint on
  sieves, so it preserves `iSup`; without that the per-piece obligations would be about a
  different sieve than the one the pullback of the target names.

None of the three mentions `pic⁰`, a chart, or a divisor.  That is the point: the
affine-to-general passage for antecedent 2 is a fact about the site, and mixing it with the
geometry is what made it look like part of the geometry's price.

## What this does and does not buy

It buys the quantifier, and only the quantifier.  `chartsCoverLocally_of_affineLocal` below
asks for the pointwise datum **only over affine schemes**, and produces
`ChartsCoverLocally` at every test; `isLocallySurjective_sigmaDesc_of_affine` composes that
with B-6.  So a producer may now assume its test is `Spec S` and reach for
`divFamZarAffineEquiv`, `DivisorFamilyFieldSurj`, `effectiveDivisorClassifyZar` and the rest
of the ring-indexed machinery directly.

It does **not** produce the datum at an affine test.  That is B-5's geometry and it remains
open; per `Picard/Pic0ChartCoveragePointwise.lean` and the `dat-b` row the residue there is
the class-side question, and per `Pic0ChartAtlasCoupling.lean` the range containment `hV` is
a further separate obligation.  What changes is that the residue is now stated where the
tree's producers live.

**On the converse, corrected.**  An earlier version of this paragraph said
`affineLocal_of_chartsCoverLocally` makes the affine and general forms "equivalent", and cited
that as discharging the `reduction-needs-its-converse` safeguard.  It does not: that
declaration is `rfl`-equal to `pointwise_of_chartsCoverLocally`, its `[IsAffine Y]` binder is
never used, and the direction it certifies is the *free* one — general pointwise data gives the
affine data by `fun Y _ s y => h Y s y`.  So the affine form is a genuine **weakening** of the
general one, which is exactly why `chartsCoverLocally_of_affineLocal` is worth having; the
honest certificate is that theorem, not a no-op converse (audit `I-1023`).  The converse is
kept only as the affine-test instance of the pointwise extraction, which is what it is.

**On the atlas, and this is the sharper limit.**  Nothing here pins `V`.  The statements below
take an arbitrary family `f`, which is what makes the site content reusable — but a consumer
must supply coverage at the *same* `V` at which antecedent 1 was certified, and `ajcr-p1`
measured both ends of that range to be bad: `hf` is free at `V = ⊥` (`isChartUniv_bot`, with a
construction that never mentions the Abel chart), while `V = ⊤` returns the unrestricted
certificate that three headers call false.  So any workable `V` is a proper intermediate open,
CHART-U(b)'s openness is load-bearing, and the pair `(huniv V, hcov V)` has **no measured
inhabitant at any `V`** (`I-1012`).  Two bad endpoints are two refutations, not a non-vacuity
check.

## Main declarations

* `AlgebraicGeometry.mem_zariskiTopology_of_pullback_affine` — **the site fact**, with no
  presheaf and no chart: a sieve on `T` is covering as soon as its pullback along every map
  from an affine scheme in a cover of `T` is covering.
* `AlgebraicGeometry.chartsCoverLocally_of_affineLocal` — **the reduction**: pointwise
  coverage over affine tests only gives `ChartsCoverLocally` at every test.
* `AlgebraicGeometry.isLocallySurjective_sigmaDesc_of_affine` — the composite with B-6, i.e.
  the instance `pic0RepresentableByOfCharts` consumes, from affine-test data alone.
* `AlgebraicGeometry.affineLocal_of_chartsCoverLocally` — the converse, so the affine form
  is not a strengthening.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
variable [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The site fact -/

/-- **A sieve is covering as soon as it is covering after pullback to affine pieces.**

Stated for an arbitrary sieve on an arbitrary scheme, because that is all it uses.  The
cover is `Scheme.affineCover`, whose members are affine by
`Scheme.isAffine_affineCover`, and the deduction is `GrothendieckTopology.transitive`
against the presieve the cover generates.

This is the step the coverage chain was missing: it says the Zariski-local-surjectivity
obligation may be discharged one affine piece of the test at a time. -/
theorem mem_zariskiTopology_of_pullback_affine {T : Scheme.{u}} (S : Sieve T)
    (h : ∀ (j : T.affineCover.I₀), S.pullback (T.affineCover.f j) ∈
      Scheme.zariskiTopology (T.affineCover.X j)) :
    S ∈ Scheme.zariskiTopology T := by
  have hcov : (Sieve.generate (Presieve.ofArrows T.affineCover.X T.affineCover.f))
      ∈ Scheme.zariskiTopology T :=
    Scheme.mem_grothendieckTopology_iff.mpr ⟨T.affineCover, Sieve.le_generate _⟩
  refine Scheme.zariskiTopology.transitive hcov S ?_
  rintro Y g ⟨V, a, b, ⟨j⟩, rfl⟩
  rw [Sieve.pullback_comp]
  exact Scheme.zariskiTopology.pullback_stable a (h j)

/-! ## The reduction -/

variable (C) in
/-- **THE AFFINE-TEST REDUCTION**: pointwise coverage over affine tests gives
`ChartsCoverLocally` at every test.

The hypothesis is `chartsCoverLocally_of_pointwise`'s, with `[IsAffine Y]` added and
nothing else changed.  So a coverage producer may assume its test is affine — hence, through
`divFamZarAffineEquiv`, that its divisor data lives over a *ring*, which is where every
producer in this project is stated. -/
theorem chartsCoverLocally_of_affineLocal {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (h : ∀ (Y : Scheme.{u}) [IsAffine Y] (s : (pic0SigmaSheaf C).1.obj (op Y)) (y : ↥Y),
      ∃ (W : Y.Opens) (_ : y ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ X i),
        (f i).app (op (W : Scheme.{u})) x = (pic0SigmaSheaf C).1.map (W.ι).op s) :
    ChartsCoverLocally C f := by
  intro T s
  refine mem_zariskiTopology_of_pullback_affine _ fun j => ?_
  -- the pullback of the supremum is the supremum of the pullbacks, and each is the image
  -- sieve of the RESTRICTED section — so the obligation at the affine piece is exactly the
  -- affine instance of the hypothesis
  have hpb : (⨆ i, Presheaf.imageSieve (f i) s).pullback (T.affineCover.f j)
      = ⨆ i, Presheaf.imageSieve (f i)
          ((pic0SigmaSheaf C).1.map (T.affineCover.f j).op s) := by
    -- `Sieve.pullback` preserves `iSup` (it is a left adjoint), and per index it turns the
    -- image sieve of `s` into that of `s` restricted along the cover map
    simp only [← Presheaf.pullback_imageSieve]
    ext Y g
    simp only [iSup, Sieve.sSup_apply, Sieve.pullback_apply]
    aesop
  rw [hpb]
  -- the piece is affine (`Scheme.isAffine_affineCover`), so the hypothesis applies AT IT — note
  -- `chartsCoverLocally_of_pointwise` cannot be cited here, since it quantifies over all tests
  -- and would demand the datum at the non-affine ones too; the site bridge is what is reused
  choose W hW i x hx using h (T.affineCover.X j)
    ((pic0SigmaSheaf C).1.map (T.affineCover.f j).op s)
  exact mem_zariskiTopology_iSup_of_pointwise _ W hW i fun y => ⟨x y, hx y⟩

variable (C) in
/-- **B-5 over affine tests ⟹ B-6**: the local-surjectivity instance
`pic0RepresentableByOfCharts` consumes, from affine-test coverage data alone. -/
theorem isLocallySurjective_sigmaDesc_of_affine {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (h : ∀ (Y : Scheme.{u}) [IsAffine Y] (s : (pic0SigmaSheaf C).1.obj (op Y)) (y : ↥Y),
      ∃ (W : Y.Opens) (_ : y ∈ W) (i : ι) (x : (W : Scheme.{u}) ⟶ X i),
        (f i).app (op (W : Scheme.{u})) x = (pic0SigmaSheaf C).1.map (W.ι).op s) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) :=
  isLocallySurjective_sigmaDesc f (chartsCoverLocally_of_affineLocal C f h)

/-! ## The converse -/

variable (C) in
/-- **The affine form is not a strengthening**: `ChartsCoverLocally` gives back, over each
affine test, a cover on whose members some chart hits the section.

Read the carrier honestly, exactly as `pointwise_of_chartsCoverLocally` does: the sieve
condition returns a cover by *arbitrary* schemes with open-immersion maps, not by opens of
the test, so the converse produces a cover map where the hypothesis consumed an opens
inclusion.  For the purpose this serves — that the affine-only hypothesis is available, not
chosen for provability — a cover map is exactly as good. -/
theorem affineLocal_of_chartsCoverLocally {ι : Type u} {X : ι → Scheme.{u}}
    (f : ∀ i, yoneda.obj (X i) ⟶ (pic0SigmaSheaf C).1)
    (h : ChartsCoverLocally C f) (Y : Scheme.{u}) [IsAffine Y]
    (s : (pic0SigmaSheaf C).1.obj (op Y)) :
    ∃ (𝒰 : Y.Cover.{u} (Scheme.precoverage @IsOpenImmersion)),
      ∀ j : 𝒰.I₀, ∃ (i : ι) (x : 𝒰.X j ⟶ X i),
        (f i).app (op (𝒰.X j)) x = (pic0SigmaSheaf C).1.map (𝒰.f j).op s :=
  pointwise_of_chartsCoverLocally C f h Y s

end

end AlgebraicGeometry
