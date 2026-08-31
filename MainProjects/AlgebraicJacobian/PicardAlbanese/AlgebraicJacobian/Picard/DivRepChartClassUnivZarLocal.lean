/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivQuot
import AlgebraicJacobian.Picard.DivSchemeCertZarPointwise
-- The four declarations this file's docstring reasons ABOUT rather than uses:
-- `forall_not_isCertified_of_straddling` (the no-go), `forall_noLeak_of_forall_subset_or_disjoint`
-- and `forall_subset_or_disjoint_of_isPreconnected` (the swallow-or-miss route), and
-- `forall_noLeak_of_forall_supportLocus_subset` (the wrapper).  Imported so every cited name is
-- IN THIS FILE'S IMPORT CLOSURE and `#check`s here, not merely greppable elsewhere: a name that
-- exists in source but not in scope is a nonexistent citation, and grep cannot tell the
-- difference (measured on the first version of this header, which cited all four out of scope).
import AlgebraicJacobian.Picard.DivisorFamilyAffStrict
import AlgebraicJacobian.Picard.DivSchemeCertZarConn
import AlgebraicJacobian.Picard.DivSchemeCertZarSwallow
import AlgebraicJacobian.Picard.DivSchemeCertZarTube

/-!
# U2's class half: the no-go DOES reach the Zariski-local pin, and its input narrows

`Picard/DivRepChartClassUnivAny.lean:223-231` carries a warning that the roadmap leaf
`…divrep.u2` and three inbox items have since quoted as the leaf's price:

> the hypothesis `HasCertifiedAdaptation` is **refuted** by
> `forall_not_isCertified_of_straddling` … So this theorem is a sound *reduction* whose
> hypothesis may be false; do not read it as "U2 is one certificate away".

The warning is correct, and **it does reach the Zariski-local pin as well** — but only in a
NARROWED form, and the narrowing is what this file records.

## What the no-go does and does not need

*A first draft of this file claimed the no-go could not reach the pin, on the grounds that no
lemma carries `¬ IsLocallyCertified` and that the only landed implication runs
`isLocallyCertified_of_isCertified`, i.e. refuted-side → pin.  Both halves of that are true and
the conclusion drawn from them was wrong; the correction is kept in place of the claim because
the reasoning is the reusable part.*

No bridge lemma is needed, because `forall_not_isCertified_of_straddling`
(`Picard/DivisorFamilyAffStrict.lean:127`) takes its base ring as a **section variable** and
its system as an implicit.  It therefore instantiates directly at
`R := Localization.Away r` with the **pulled** system, which is exactly the binder
`IsLocallyCertified` (`Picard/DivisorFamilyZar.lean:71`) uses.  A no-go stated over section
variables is a *schema*, not a statement about one ring, and "the pin quantifies over a
different ring" buys nothing against it.

What the away form *does* buy is a strictly smaller refuting input.  To kill the pin one now
needs the two straddling witnesses **inside a single fibre** — the existential picks `r` with
`r ∉ p`, so witnesses lying over `p` survive whichever `r` is offered, but witnesses at
unrelated primes can be shrunk away.  Global straddling refutes
`HasCertifiedAdaptation`; only one-fibre straddling refutes the pin.  Two sibling headers state
this in prose already (`Picard/DivSchemeCertZarC1.lean:32`,
`Picard/DivSchemeCertZarVerdict.lean:25`: no Zariski shrink separates the witnesses).

## What this file lands

The per-prime route already in the tree
(`ThetaGeneratorSeed.isLocallyCertified_of_forall_prime_exists_certified_adaptation`,
`Picard/DivSchemeCertZarPointwise.lean:162`) produces the pin from away-localized
certificates.  This file instantiates it at the high-window universal seed, so that U2's
class half is stated at the binder a producer can actually target, and names the refuting
input that binder still admits.

## Main declarations

* `AlgebraicGeometry.PointwiseAchiever.ForallPrimeAwayCertified` — the away form of the
  class obligation, stated so that the ring each adaptation lives over is visible.
* `AlgebraicGeometry.PointwiseAchiever.divFamZarUnivOfForallPrimeAway` — the `DivFamZar`
  class at the universal point from it, with no certificate over `R_Z` in the input.
* `AlgebraicGeometry.ThetaGeneratorSeed.isLocallyCertified_of_isCertified_not_conversely`
  — the direction record: the refuted side implies the pin.  Kept, with its name's `_not_
  conversely` read as a statement about the *implication*, not as a claim that the no-go
  fails to reach the pin — it does reach it, by instantiation at the away ring.
* `AlgebraicGeometry.ThetaGeneratorSeed.side_straddle_gives_chart_separated_pieces` — the
  probe's correct shape: opposite `side` values already separate the charts, so what is
  measurable is the `side` function, not a support locus.

## What this does NOT do, stated exactly

It produces **no certificate**, at no prime, so **no gate clears** and `rep` remains
undischarged.  It does not make the class half easier; it makes the *refuting* input harder,
which is a smaller and less exciting claim than the one this file's first draft made.

**The away hypothesis has no witness at any prime**, here or anywhere in the tree, and it is
refutable exactly when the universal seed's support straddles within one fibre.

**THE PROBE THIS SEAM STILL OWES, in the shape that is worth running.**  Nothing in the tree
compares `univSeed`'s support to the pinned charts, and the leaf is unpriced in both directions
until something does — two rounds have argued about whether a refutation reaches its target
instead of checking whether its antecedent holds.  But "does `univSeed` straddle?" is the wrong
spelling, and `side_straddle_gives_chart_separated_pieces` below says why:

* every seed **piece** is confined to one pinned chart *by construction* — `piece_le` is
  `basicOpen_le` at `relPinnedChart C R π (D.side z)`, so this is a fact about the *type*
  `ThetaGeneratorSeed` and there is nothing seed-specific to measure;
* but `localEquations` builds a **pointed** cover, one member per point, with `side` a function
  *of the point*.  So the support locus may straddle both charts globally while every piece is
  chart-confined.  Those are different statements.

The measurement is therefore about the `side` **function**, not about a support computation:
*do two points of the support take opposite sides?*  That is where a lane should spend the
round.  (Established by `review-ajcr`, inbox `I-1003`; re-derived here rather than taken on
report, and the transport is the theorem below.)

**Neither direction is settled by any of this, and the asymmetry is easy to mis-quote.**
Per-piece chart-confinement together with a `side` *function* **permits** global straddling; it
does not **produce** it.  So "the seed is chart-confined" must not be read as "it straddles",
and equally must not be read as "it cannot" — the first is what a producer needs ruled out, the
second is what a producer would need proved, and this file supplies neither.

**One further thing unmeasured here, and it may be decisive** (`review-ajcr`, `I-1003`):
`ThetaGeneratorSeed` types its pieces *into* the pinned charts, which is the shape protection
`I-0492` clause 3 names as what made the earlier cheaper option vacuous.  If U2's class half
routes through the seed at all, it is on the **chart-typed** side of the widening by
construction, and the away-localization argument above inherits that confinement.  Were that so,
the retraction at the top of this file would have a *structural* cause rather than a proof-level
one.  Not measured here; worth testing before another round is spent on the away route.

**Do NOT read the pinned-chart geometry as an obstruction.**  The certificate assemblers
(`DivisorAdaptation.isCertified_of_noLeak_kernel_spanning`, `Picard/DivSchemeCertUniv.lean:104`)
consume a *swallow-or-miss* clause, and a **disjoint** piece is its harmless branch:
`forall_noLeak_of_forall_subset_or_disjoint` accepts it, and
`forall_subset_or_disjoint_of_isPreconnected` (`Picard/DivSchemeCertZarConn.lean:128`) already
produces the disjunction for a connected support.  The `∀ j, supp ⊆ pieces j` shape of
`forall_noLeak_of_forall_supportLocus_subset` (`Picard/DivSchemeCertZarTube.lean:142`) is a
convenience wrapper, and it is the wrapper — not the interface — that is degenerate on a cover
with two disjoint pieces.  This paragraph replaces a guard theorem that audited the wrapper and
inferred a limit on the assembler; the inference was wrong and the theorem is withdrawn.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian ThetaGeneratorSeed

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule
attribute [local instance 10000] relCurve.instOver

/-! ## The direction record -/

namespace ThetaGeneratorSeed

section Direction

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))} [IsProper C.hom]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

/-- **The refuted side implies the pin** — the whole reason
`forall_not_isCertified_of_straddling` does not bear on U2's class half.

This is `isLocallyCertified_of_isCertified` restated with its role named.  The point is the
*direction*: a refutation of `(D.divisorAdaptation hD).IsCertified n` is a refutation of this
theorem's **hypothesis**, and an implication whose hypothesis is false is still true and says
nothing about its conclusion.  Stated here because the leaf's recorded price reads the
refutation as though it travelled forwards. -/
theorem isLocallyCertified_of_isCertified_not_conversely [IsNoetherianRing R] {n : ℕ}
    {D : ThetaGeneratorSeed C R π a K} (hD : D.IsGenerator)
    (hc : (D.divisorAdaptation hD).IsCertified n) :
    IsLocallyCertified C R π n (D.localEquations hD) :=
  D.isLocallyCertified_of_isCertified hD hc

end Direction

end ThetaGeneratorSeed

/-! ## The probe's correct shape: `side`, not the support -/

namespace ThetaGeneratorSeed

section SideStraddle

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π] {a : ℕ}
variable {K : Submodule R (relThetaSections C R π a)}

/-- **Opposite `side` values put two pieces in opposite pinned charts** — so the straddling
datum the no-go consumes is available from the seed's `side` *function*, with no support
computation.

This is the transport that fixes the shape of the probe `…divrep.u2` owes.  Piece confinement
itself is free and carries no information: `D.piece_le z` holds for **every** seed at **every**
point, being `basicOpen_le` into `relPinnedChart C R π (D.side z)`.  What is *not* free is
whether the pointed cover of `D.localEquations` — one member per point, `side` varying with the
point — actually takes both values on the support.  That, and not "does the support straddle",
is the measurable question.

Nothing here claims the hypothesis holds for the high-window universal seed.  It says that if a
lane exhibits two support points with opposite sides, the chart separation the no-go wants
follows immediately, and that a lane which instead sets out to compute a support locus is
measuring the wrong object. -/
theorem side_straddle_gives_chart_separated_pieces (D : ThetaGeneratorSeed C R π a K)
    {z z' : relCurve C R} (hz : D.side z = false) (hz' : D.side z' = true) :
    D.piece z ≤ relPinnedChart C R π false ∧ D.piece z' ≤ relPinnedChart C R π true :=
  ⟨hz ▸ D.piece_le z, hz' ▸ D.piece_le z'⟩

end SideStraddle

end ThetaGeneratorSeed

/-! ## The refuting input, narrowed to one fibre

The no-go instantiates at the away ring (see the module docstring), so the away form is
refutable — but its two straddling witnesses must now lie over a **single** base prime, since
the existential chooses `r` outside that prime and witnesses over it survive the shrink.  That
narrowing is the whole difference between refuting `HasCertifiedAdaptation` and refuting the
pin, and it is what a producer's geometry has to rule out. -/

namespace PointwiseAchiever

section ZarLocalUniversal

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable {pi : C.left ⟶ P1 k} [IsFinite pi] [IsDominant pi]

noncomputable local instance instOverCleftUnivZarLocal :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))]
  [QuasiCompact (C.left ↘ Spec (.of k))]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g r1 r2 : Nat)
variable (b1 : Module.Basis (Fin r1) k
  ↥(Scheme.divisorSections k
    (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(Scheme.divisorSections k
    ((windowS_choice pi hpi g • fiberWeilDivisor pi) +
      (windowM_choice pi hpi g • fiberWeilDivisor pi)) ⊤))
variable (i : (glueData k g r1).J) (j : (glueData k g r2).J)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
  (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))

local notation "RZ" => DivCarveChartRing k
  (windowS_choice pi hpi g • fiberWeilDivisor pi)
  (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1 b2 i j

/-- Abbreviation for the universal seed's local-equation system, so the away hypothesis
below can be stated without repeating the generator clause four times. -/
noncomputable abbrev univSystem (hb : 0 < windowBound pi hpi) :
    (relCurve C RZ).LocalEquations :=
  (univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).localEquations
    (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)

/-- **The per-prime away hypothesis**, named: at every prime of the chart ring some basic
open carries a certified chart-typed adaptation of the *pulled* universal system.

This is the hypothesis that replaces `HasCertifiedAdaptation`.  It is not an instance of
`forall_not_isCertified_of_straddling`'s `∀`: that quantifier ranges over adaptations of the
system over `R_Z` itself, while every adaptation here lives over a `Localization.Away r` and
adapts the pullback along `relCurveMap`. -/
def ForallPrimeAwayCertified [IsNoetherianRing RZ] (hb : 0 < windowBound pi hpi) : Prop :=
  ∀ p : PrimeSpectrum RZ, ∃ r, r ∉ p.asIdeal ∧
    haveI : IsOpenImmersion (relCurveMap C RZ (Localization.Away r)) :=
      isOpenImmersion_relCurveMap_away C RZ (Localization.Away r) r
    ∃ A : DivisorAdaptation C (Localization.Away r) pi
        ((univSystem C hpi g r1 r2 b1 b2 i j hO hchi hb).pullback
          (relCurveMap C RZ (Localization.Away r))
          (Scheme.LocalEquations.germ_pullbackEqn_mem_nonZeroDivisors_of_isOpenImmersion
            (relCurveMap C RZ (Localization.Away r))
            (univSystem C hpi g r1 r2 b1 b2 i j hO hchi hb))),
      A.IsCertified g

/-- **U2's class half from the away hypothesis** — the locally certified class over the
`Z(♦)`-chart ring, with no certificate over `R_Z` anywhere in the input. -/
noncomputable def divFamZarUnivOfForallPrimeAway [IsNoetherianRing RZ]
    (hb : 0 < windowBound pi hpi)
    (h : ForallPrimeAwayCertified C hpi g r1 r2 b1 b2 i j hO hchi hb) :
    DivFamZar C RZ pi g :=
  (univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb).divFamZar_of_forall_prime_away_certified
    (isGenerator_univSeed C hpi g r1 r2 b1 b2 i j hO hchi hb)
    (fun p => by
      obtain ⟨r, hrp, A, hA⟩ := h p
      haveI : IsOpenImmersion (relCurveMap C RZ (Localization.Away r)) :=
        isOpenImmersion_relCurveMap_away C RZ (Localization.Away r) r
      exact ⟨r, hrp, ⟨_, A, hA⟩, Scheme.LocalEquations.divEq_refl _⟩)

end ZarLocalUniversal

end PointwiseAchiever

end AlgebraicGeometry
