/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivisorFamilyAffAssemble
import AlgebraicJacobian.Picard.DivisorFamilyAffSeedEndpoint
import AlgebraicJacobian.Picard.DivisorFamilyAffGlueZar

/-!
# THE SEED-LEVEL WIDENED GATE: geometry produces a `DivFamZarAff` class

Roadmap leaves `AJCR.w4-rep.datum.dat-d.ddr.certificate.cert-assemble` /
`…cert-collapse`, on the widened (R2) carrier of protection I-0492.

## The gap this closes, measured rather than asserted

At `a41644c36` the widened layer had thirty files and, by declaration reference:

* exactly **two** of them mentioned `ThetaGeneratorSeed` — `…AffFibre.lean` (obligation 4(i))
  and `…AffSeedEndpoint.lean` (the over-`R` endpoint) — and **neither** produced
  `IsLocallyCertifiedAff` or `DivFamZarAff`;
* crossed the other way, **zero** files mentioning `IsLocallyCertifiedAff`/`DivFamZarAff`
  mentioned `ThetaGeneratorSeed`.

So the only producers of a widened *value* were `mapAlg` of an existing one and the trivial
one-member glue: **nothing turned geometry into a widened class.**  The chart-typed lane has
that join twice — `ThetaGeneratorSeed.isLocallyCertified_of_forall_prime_exists_certified_adaptation`
(`DivSchemeCertZarPointwise.lean:162`) and `…isLocallyCertified_of_forall_away_certified`
(`DivSchemeCertZarSeed.lean:115`).  This file supplies the widened counterparts, so a DD-R
consumer restated on `divFunctorAff` (`DivRepGlobalAffLift.lean`) has something to consume.

## Why the composition is not a restatement, and where the work actually was

The over-`R` endpoint `exists_isCertified_of_seed_of_swallowing_affineOpen` returns
`∃ Dc A, A.IsCertified n` — an adaptation of `D.localEquations hD` **over `R` itself**.  The
pointwise assembler `isLocallyCertifiedAff_of_forall_prime_certified_adaptation` wants, at each
prime, a certificate over `Localization.Away r` for the **pulled** system.  Those are different
statements and there is no `ThetaGeneratorSeed` base change in this project, so the away route
would need the seed's fibre datum transported to a localized base — machinery nobody has built.

The composition below avoids needing it, and the reason is the shape of `IsLocallyCertifiedAff`
rather than any new geometry: `CertifiedDivisorFamilyAff.isLocallyCertifiedAff`
(`…AffGlueZarKit.lean:575`) already witnesses the predicate at the **trivial one-member cover**
`g = ![1]`, where `Localization.Away (1 : R)` receives the system by `mapAlg` and the required
`DivEq` is reflexivity.  So an over-`R` certificate is *already* a local one, and the seed
endpoint is exactly an over-`R` certificate.  No away-base seed transport is required for this
direction — which is the honest reason this lands in a session rather than a wave.

**What that does and does not buy.** It gives the widened lane a producer from geometry, which
it did not have.  It does **not** make the away-localized route unnecessary: a seed whose
degree datum is only available *after* shrinking the base still needs the per-prime form, and
that form is the general `isLocallyCertifiedAff_of_forall_prime_certified_adaptation` — stated,
landed, and still without a seed-level producer.  The two `_of_forall_prime` variants below take
the per-prime certificate as a hypothesis for exactly that reason; they are the widened
counterparts of the chart-typed gate's shape, not a discharge of it.

## The obligations, still visible

Nothing here hides an obligation inside a `LocalEquations` (protection I-0492 clause 4):

* obligation 4(i), fibrewise-finite support, does **not** appear — it is discharged from the
  seed by `ThetaGeneratorSeed.affAdaptation_fibre_regular` (`…AffFibre.lean`), inside the
  endpoint;
* the subordinate Stacks `0B8B` input is the explicit `hW`/`hsub`/`hWle` triple, assumed per
  I-0492 clause 2;
* the degree datum is the explicit `hrank`, read at the swallowing piece.

## What IS still chart-typed here, measured and stated rather than glossed

Note before re-checking any of this: the table below **names** the constants it reports absent, so
`grep FinCoverData` on this file returns hits from the claim itself (inbox `I-0717`: an
absence-claim docstring breaks the grep that would verify it). That is harmless *here* only because
the measurement is a **declaration-dependency closure**, which reads proof terms and cannot see a
comment. Re-verify it the same way, not with a text search.

A declaration-closure probe (the calibrated form of ADDENDUM 10 §10.3 — controls
`FinCoverData.toAffCoverData` / `.toChartTyping`, both of which fire) reports for
`divFamZarAff_of_swallowing_affineOpen` (closure 4780) and `divFunctorAffSection` (4887):

| probe | in closure? |
|---|---|
| `FinCoverData`, `FinCoverData.mk` | **no** |
| `ChartTyping` | **no** |
| `relCover_sup` | **no** |
| `AffCoverData` | yes (the widened carrier — expected) |
| `relPinnedChart` | **YES**, and only through `ThetaGeneratorSeed` |

So the honest reading, in both directions:

* **The certificate side is chart-free.** No `FinCoverData`, no `ChartTyping`, and in particular
  no `relCover_sup` — which matters specifically, because `relCover_sup` is the step that turned
  "misses `V₀`" into "lies inside `V₁`", i.e. the exact mechanism the refuted fixed-pair repair
  depended on (spec ADDENDUM 3 §2).  Nothing here can reconstruct it: the cover has `m` pieces and
  no distinguished pair.
* **The SEED is not chart-free, and that is not something this file fixes.**
  `ThetaGeneratorSeed` (`DivSchemeFamily.lean:74`) has fields `side : relCurve C R → Bool` and
  `h : ∀ z, Γ(relCurve C R, relPinnedChart C R π (side z))`, so its pieces *are* basic opens of
  the pinned charts.  Its `LocalEquations` cover therefore consists of chart-typed pieces even
  though the certificate's cover does not.

This is a genuine limit on the claim, not a violation of I-0492 clause 3, and the difference is
worth being precise about.  Clause 3 forbids the *certificate clauses* from requiring the pieces
to lie in a fixed pair of charts — that is what made the per-piece statement upgrade to a chart
statement, and that is gone.  What remains is that the *input datum* this project happens to
produce systems from is chart-indexed; the widened route consumes it without ever needing the
containment, which is why the subordinate `0B8B` open `W` is an arbitrary affine open with no
relation to `V₀`/`V₁`.  A chart-free seed notion would remove the last occurrence, and no consumer
of this file needs one.

## Main declarations

* `AlgebraicGeometry.ThetaGeneratorSeed.isLocallyCertifiedAff_of_swallowing_affineOpen` — the
  gate: seed + `0B8B` + degree ⟹ `IsLocallyCertifiedAff`.
* `AlgebraicGeometry.ThetaGeneratorSeed.divFamZarAff_of_swallowing_affineOpen` — **the class**,
  the object a widened DD-R consumer receives.
* `AlgebraicGeometry.ThetaGeneratorSeed.isLocallyCertifiedAff_of_forall_prime_certified_adaptation`
  and `…divFamZarAff_of_forall_prime_certified_adaptation` — the seed-level per-prime forms,
  the widened counterparts of `DivSchemeCertZarPointwise.lean:162`/`:181`.
* `AlgebraicGeometry.ThetaGeneratorSeed.picClass_divFamZarAff_of_swallowing_affineOpen` — the
  class's Picard class is the system's, so the Abel hook DAT-C consumes it unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161), so the pinned synthesis
depth must be set in-file for the faithful per-file check. -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] {a : ℕ}
variable {K : Submodule R (relThetaSections C R pi a)}

namespace ThetaGeneratorSeed

variable {D : ThetaGeneratorSeed C R pi a K}

/-! ## From an over-`R` widened certificate to the widened pin -/

/-- **A widened certificate over `R` is a widened local certificate**, for the seed's own
system.  Bridging lemma: `CertifiedDivisorFamilyAff.isLocallyCertifiedAff` witnesses the pin at
the one-member cover `g = ![1]`, and a cover/adaptation/certificate triple over `R` is exactly
a `CertifiedDivisorFamilyAff`.

This is the widened counterpart of `isLocallyCertified_of_isCertified`
(`DivSchemeCertZarSeed.lean:150`), and like it, it is a genuine weakening in the useful
direction: a global certificate suffices, and the per-prime form remains available for a
divisor whose degree datum only appears after shrinking the base. -/
theorem isLocallyCertifiedAff_of_isCertified [IsProper C.hom] [IsNoetherianRing R] {n : ℕ}
    (hD : D.IsGenerator)
    (h : ∃ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD)),
      A.IsCertified n) :
    IsLocallyCertifiedAff n (D.localEquations hD) := by
  obtain ⟨Dc, A, hA⟩ := h
  exact CertifiedDivisorFamilyAff.isLocallyCertifiedAff
    (⟨D.localEquations hD, Dc, A, hA⟩ : CertifiedDivisorFamilyAff C R n)

/-! ## The gate -/

/-- **THE SEED-LEVEL WIDENED GATE.**  From a theta-generator seed, the subordinate Stacks
`0B8B` input, and the degree datum at the swallowing piece, the seed's local-equation system is
**widened**-locally certified in degree `n`.

Every hypothesis is one protection I-0492 names, and none of them is a chart:

* `hW`/`hsub`/`hWle` — the subordinate `0B8B` input, an affine open `W ⊇ supp d` inside one
  member of `d.cover` (clause 2: USE, do not re-derive);
* `hrank` — the degree datum, read at the piece that swallows the support (clause 4's honest
  residue; it cannot come from anywhere else).

Obligation 4(i) is absent because it is *discharged*: `affAdaptation_fibre_regular` supplies it
from the seed at every widened cover and adaptation, inside
`exists_isCertified_of_seed_of_swallowing_affineOpen`.

**No hypothesis on `|P¹(k)|` occurs here or on the route** — that is the field-uniformity R2 was
chosen for over a field-size hypothesis (I-0492's "WHY R2"). -/
theorem isLocallyCertifiedAff_of_swallowing_affineOpen [IsProper C.hom] [IsNoetherianRing R]
    {n : ℕ} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (j₀ : Dc.index),
      (D.localEquations hD).supportLocus ⊆ (Dc.pieces j₀ : Set (relCurve C R)) →
      (∀ j : Dc.index, j ≠ j₀ →
        Disjoint (D.localEquations hD).supportLocus (Dc.pieces j : Set (relCurve C R))) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (A.colength j₀) p = n) :
    IsLocallyCertifiedAff n (D.localEquations hD) :=
  isLocallyCertifiedAff_of_isCertified hD
    (exists_isCertified_of_seed_of_swallowing_affineOpen C R hD hW hsub z₀ hWle hrank)

/-- **The `DivFamZarAff` class of a seed certified on an affine open** — the object a widened
DD-R consumer receives.  This is the widened counterpart of
`divFamZar_of_forall_prime_away_certified` (`DivSchemeCertZarPointwise.lean:181`), and it is the
first producer of a widened class from geometry rather than from another widened class. -/
noncomputable def divFamZarAff_of_swallowing_affineOpen [IsProper C.hom] [IsNoetherianRing R]
    {n : ℕ} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (j₀ : Dc.index),
      (D.localEquations hD).supportLocus ⊆ (Dc.pieces j₀ : Set (relCurve C R)) →
      (∀ j : Dc.index, j ≠ j₀ →
        Disjoint (D.localEquations hD).supportLocus (Dc.pieces j : Set (relCurve C R))) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (A.colength j₀) p = n) :
    DivFamZarAff C R n :=
  DivFamZarAff.mk (D.localEquations hD)
    (isLocallyCertifiedAff_of_swallowing_affineOpen hD hW hsub z₀ hWle hrank)

/-- **The Picard class of the gate's output is the system's own.**  Recorded because it is what
makes the class *usable*: DAT-C's Abel hook reads `picClass`, and it must not depend on which
widened cover certified the system.  It does not — `DivFamZarAff.picClass_mk` is `rfl`. -/
@[simp]
theorem picClass_divFamZarAff_of_swallowing_affineOpen [IsProper C.hom] [IsNoetherianRing R]
    {n : ℕ} (hD : D.IsGenerator)
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (hsub : (D.localEquations hD).supportLocus ⊆ (W : Set (relCurve C R)))
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀)
    (hrank : ∀ (Dc : AffCoverData C R) (A : AffAdaptation Dc (D.localEquations hD))
      (j₀ : Dc.index),
      (D.localEquations hD).supportLocus ⊆ (Dc.pieces j₀ : Set (relCurve C R)) →
      (∀ j : Dc.index, j ≠ j₀ →
        Disjoint (D.localEquations hD).supportLocus (Dc.pieces j : Set (relCurve C R))) →
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (A.colength j₀) p = n) :
    (divFamZarAff_of_swallowing_affineOpen hD hW hsub z₀ hWle hrank).picClass
      = (D.localEquations hD).picClass :=
  rfl

/-! ## The per-prime forms

These are the widened counterparts of the chart-typed gate at
`DivSchemeCertZarPointwise.lean:162`/`:181`.  They take the away-localized certificate as a
HYPOTHESIS: no seed base change exists in this project, so a producer at this shape still owes
the transport.  Stated at the seed rather than at a bare system so that a caller holding a seed
does not have to unfold `D.localEquations hD` to use the general assembler. -/

/-- **The seed-level per-prime widened gate.**  At every prime of the base it suffices to
produce an away localization carrying a certified WIDENED adaptation of the pulled seed system.

Contrast the gate above: this form is the one to use when the degree datum only becomes
available after shrinking the base, which is the situation the support tube produces.  What it
does not do is discharge the away-base fibre transport — that is the hypothesis. -/
theorem isLocallyCertifiedAff_of_forall_prime_certified_adaptation [IsNoetherianRing R] {n : ℕ}
    (hD : D.IsGenerator)
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ (Dr : AffCoverData C (Localization.Away r))
        (A : AffAdaptation Dr
          ((D.localEquations hD).pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) (D.localEquations hD)))),
        A.IsCertified n) :
    IsLocallyCertifiedAff n (D.localEquations hD) :=
  -- The `_root_` qualification is load-bearing: inside `namespace ThetaGeneratorSeed` the short
  -- name resolves to THIS declaration, so the general assembler must be named in full.
  _root_.AlgebraicGeometry.isLocallyCertifiedAff_of_forall_prime_certified_adaptation
    (n := n) h

/-- The `DivFamZarAff` class of a seed certified pointwise on the base. -/
noncomputable def divFamZarAff_of_forall_prime_certified_adaptation [IsNoetherianRing R]
    {n : ℕ} (hD : D.IsGenerator)
    (h : ∀ p : PrimeSpectrum R, ∃ r, r ∉ p.asIdeal ∧
      haveI : IsOpenImmersion (relCurveMap C R (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C R (Localization.Away r) r
      ∃ (Dr : AffCoverData C (Localization.Away r))
        (A : AffAdaptation Dr
          ((D.localEquations hD).pullback (relCurveMap C R (Localization.Away r))
            (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
              (relCurveMap C R (Localization.Away r)) (D.localEquations hD)))),
        A.IsCertified n) :
    DivFamZarAff C R n :=
  DivFamZarAff.mk (D.localEquations hD)
    (isLocallyCertifiedAff_of_forall_prime_certified_adaptation hD h)

/-! ## Non-vacuity, and the exact strength of the witness

Trap (c) of the workspace probe catalogue (`I-0442`): a theorem whose hypotheses cannot hold
jointly is vacuously true and reports clean axioms like any other, so `#print axioms` on the gate
says nothing about whether it is about anything.  The inhabitation is therefore exhibited.

**The caveat is inherited and must be stated here rather than only upstream.**  The gate's
hypotheses are exactly the endpoint's, so the endpoint's witness inhabits them — and that witness
sits at `n = 0` with an EMPTY support locus (`exists_isCertified_of_seed_of_supportLocus_empty`,
`…AffSeedEndpoint.lean`).  Its own scope paragraph says what it is worth, and the same reading
applies verbatim to the gate: it rules out the hypotheses contradicting each other outright, and
it does **not** rule out the weaker-but-real possibility that they hold only at `n = 0`.  Read the
lemma below as *"the gate is not about nothing"*, never as *"the gate is non-trivially
inhabited"*.

What is known about `n > 0` is unchanged by this file: the gate fires whenever the degree datum is
supplied at that `n`, and nothing in the hypothesis set forces `n = 0`; supplying that datum from
geometry at a specific `n > 0` is the seed layer's business.  The genuinely non-vacuous witness
would need a straddling divisor, which exists over every field (spec ADDENDUM 4 §4.3) but is out
of scope to formalise (§4.5 — it needs `Sym^g C`).  Cf. `DivisorFamilyAffStrict.lean`, whose
strictness theorem carries the identical caveat for the identical reason. -/

/-- **The gate's hypothesis set is jointly inhabited**, at the zero divisor with `n = 0`: the
support locus is empty, so the `0B8B` containment holds for any affine open inside a cover member
and every colength vanishes.

See the section note above for exactly how much this is worth — it is a non-self-contradiction
certificate, not a claim of non-trivial inhabitation. -/
theorem isLocallyCertifiedAff_of_supportLocus_empty [IsProper C.hom] [IsNoetherianRing R]
    (hD : D.IsGenerator)
    (hempty : (D.localEquations hD).supportLocus = (∅ : Set (relCurve C R)))
    {W : (relCurve C R).Opens} (hW : IsAffineOpen W)
    (z₀ : relCurve C R) (hWle : W ≤ (D.localEquations hD).cover.opens z₀) :
    IsLocallyCertifiedAff 0 (D.localEquations hD) :=
  isLocallyCertifiedAff_of_isCertified hD
    (exists_isCertified_of_seed_of_supportLocus_empty C R hD hempty hW z₀ hWle)

end ThetaGeneratorSeed

end AlgebraicGeometry
