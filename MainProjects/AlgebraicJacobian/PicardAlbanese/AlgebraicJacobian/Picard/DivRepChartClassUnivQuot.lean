/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepChartClassUnivAny
import AlgebraicJacobian.Picard.DivSchemeFrameCover

/-!
# The ε-identity does not consume a certificate: it consumes the WINDOW QUOTIENT

`Picard/DivRepChartClassUnivAny.lean` weakened U2's residue from "the `Classical.choose`n
adaptation is certified" to "*some* adaptation is certified"
(`ThetaGeneratorSeed.HasCertifiedAdaptation`).  A fresh-context review then observed that the
weakened form is **refuted** by `forall_not_isCertified_of_straddling`
(`Picard/DivisorFamilyAffStrict.lean`) whenever the seed's local equations are connected and
meet both pinned vertical fibres — that theorem concludes `∀ A n, ¬ A.IsCertified n`, so it
refutes an existential over adaptations exactly as it refutes a property of one adaptation.
The `…divrep.u2` row was left **unpriced**.

**This file re-prices it, and the answer is that the refutation misses the target.**  Unfold
what the ε-identity actually consumes:

* `divFamEps` is two `divisorWindow`s (`Picard/DivisorFamilyWindow.lean`), and
  `divisorWindow d` reads **only** `d` — no cover, no adaptation, no chart typing;
* `divisorWindow_eq_of_le` (`Picard/DivSchemeEps.lean`) is the rank engine
  `Submodule.eq_of_le_of_rankAtStalk_quotient_eq` applied to the pair
  `x.toSubmodule ≤ divisorWindow d`.  That engine's hypotheses are three module-theoretic
  facts about the **window quotient** `(R ⊗[k] H_a) ⧸ K_a(d)`.

The adaptation appears in the landed statement only as a *vehicle* for those three facts:
`windowQuotEquiv` transports them from `A.ThetaGlued a`, and `IsCertified` is what makes
`A.ThetaGlued a` finite projective of rank `g`.  Cut the vehicle out and the hypothesis is

> `(R ⊗[k] H_a) ⧸ K_a(d)` is projective over `R` of constant fibre rank `g`.

**Finiteness is not among the inputs, and that is measured rather than assumed.**  The rank
engine takes its `Module.Finite` slot at the *Grassmannian point's* quotient, which
`grFunctorAff` carries as a field; so the window side owes only projectivity and the rank
equation.  The landed chart-typed statement threads finiteness of `A.ThetaGlued a` as well —
that hypothesis is genuinely unused on the window side, and dropping it is what the
`unusedVariables` linter reported when this file first elaborated.

**Why this matters, and it is the point of the file.**  That statement mentions no
adaptation, so `forall_not_isCertified_of_straddling` does not bear on it: the no-go's proof
runs through clause **(c1)** of `IsCertified` (finiteness of the *chart-local colength*
modules forces `supportLeak = ∅`, hence confinement to one pinned chart —
`supportLocus_subset_chart_of_isCertified`).  A statement about the window quotient of `d`
is not an instance of the refuted `∀`.  So the ε-half of U2 is **open, not false**, and the
no-go's bite is confined to the *class* half.

## The honest partition this file establishes

U2 asks a producer for two things at the universal point, and only one of them is what the
no-go refutes:

| half | what it needs | vs. the no-go |
|---|---|---|
| the **ε-value** | `d`'s window quotient is projective of rank `g` | untouched: no adaptation |
| the **class** | a term of `DivFamZar C R_Z π g` (locally certified) | the refuted half |

So the `…divrep.u2` row should be read as: the ε-layer is carrier-free and no-go-immune, and
the whole remaining bite of `I-0705` is on producing the class — which is precisely the half
protection `I-0492`'s widening (R2) exists to supply.  That is a strictly sharper statement
than "unpriced", and it is what tells the certificate lane which face to widen.

## Main declarations

* `AlgebraicGeometry.divisorWindow_eq_of_le_of_quotientData` — the ε-projection identity's
  window form from the window quotient alone: no `DivisorAdaptation`, no `IsCertified`.
* `AlgebraicGeometry.divisorWindow_eq_of_le_of_isCertified_of_quotientData` — the landed
  chart-typed statement recovered as a corollary, so the generalisation is machine-checked
  rather than asserted.
* `AlgebraicGeometry.divFamEps_eq_of_le_of_quotientData` — the ε-**pair** identity for an
  arbitrary `F : DivFam C R π g`, from window-quotient data at the two pinned windows.  This
  is the form a widened producer can feed, and it never mentions a carrier.

## What this does NOT do

It produces no certificate, no adaptation and no class, so **no gate clears**: nothing here
lets a consumer instantiate `DivRepAffinePullback`.  It re-partitions the debt and removes a
*refutation* from one half of it.  Critical-path §7.6 (L8) is untouched.

**The honest limit of the headline, and it is the probe this file does not run.**  "The ε-half is
open, not false" is a claim about the **no-go**: `forall_not_isCertified_of_straddling` does not
bear on a hypothesis that names no adaptation.  It is *silent about satisfiability*.  The mirror
risk is real and unmeasured: if the window quotient at the universal point can never be
projective of constant rank `g`, then this file has reduced U2's ε-half to a **false**
hypothesis — and such a reduction passes every `sorry` census and every axiom probe, because it
is then a theorem.

Note the asymmetry with the junk-witness probe that refuted DAT-J's Abel square
(`Picard/JacobianDataAbelSquareVacuity.lean`): *that* residue was vacuous because its witness was
**consumer-chosen**.  Here the window quotient is determined by `d`, so vacuity is impossible and
satisfiability is the only live failure mode.  A reduction owes both checks; this one carries
"not silently stronger" (the corollary above, which recovers the landed statement) and owes the
satisfiability one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

open Scheme Grassmannian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
  Scheme.functionFieldOverModule

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {π : C.left ⟶ P1 k} [IsFinite π]

noncomputable local instance instOverCleftEpsQuot :
    C.left.Over (Spec (.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (.of k))] [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (.of k))] [QuasiCompact (C.left ↘ Spec (.of k))]
  [IsDominant π]

/-! ## The window form, with the adaptation removed -/

section WindowQuot

variable {a g : ℕ} {d : (relCurve C R).LocalEquations}

/-- **The ε-projection identity's window form, from the WINDOW QUOTIENT alone.**

A Grassmannian point `x` contained in the window submodule `K_a(d)` *equals* it as soon as
the window quotient `(R ⊗[k] H_a) ⧸ K_a(d)` is projective over `R` of constant fibre rank
`g`.  No `DivisorAdaptation`, no `IsCertified`, no cover, no chart typing — and no finiteness
either (the engine's `Module.Finite` slot is the Grassmannian point's own field).

This is `divisorWindow_eq_of_le` (`Picard/DivSchemeEps.lean`) with its vehicle removed.  That
statement threads an adaptation `A` and asks for finiteness/projectivity/rank of
`A.ThetaGlued a`; `windowQuotEquiv` then transports those to the quotient, which is the only
place they are used.  Stating them at the quotient is therefore a strict weakening, and it is
the weakening that matters: the standing refutation
`forall_not_isCertified_of_straddling` quantifies over `DivisorAdaptation`s, and this
hypothesis mentions none — see the module docstring. -/
theorem divisorWindow_eq_of_le_of_quotientData
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (x : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) g R)
    (hproj : Module.Projective R
      ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
        divisorWindow d hH1))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk
        ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          divisorWindow d hH1) p = g)
    (hle : x.toSubmodule ≤ divisorWindow d hH1) :
    divisorWindow d hH1 = x.toSubmodule := by
  haveI := hproj
  refine (Submodule.eq_of_le_of_rankAtStalk_quotient_eq hle fun p => ?_).symm
  rw [x.rankAtStalk_eq p, hrank p]

/-- **The landed chart-typed statement is a corollary** — recorded as a lemma so that the
generalisation above is machine-checked rather than asserted in prose.  The three
window-quotient facts come from the certificate through `windowQuotEquiv`, exactly as in the
landed proof; what the corollary shows is that nothing else in that proof used `A`. -/
theorem divisorWindow_eq_of_le_of_isCertified_of_quotientData
    (A : DivisorAdaptation C R π d) (hc : A.IsCertified g)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (x : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) g R)
    (hsurj : Function.Surjective (A.thetaGluedEval a))
    (hle : x.toSubmodule ≤ divisorWindow d hH1) :
    divisorWindow d hH1 = x.toSubmodule := by
  -- the two window-quotient facts, transported off the certificate by `windowQuotEquiv`.
  -- The `Module.Finite`/`Module.Projective` slots of `A.ThetaGlued a` are certificate
  -- CONSEQUENCES rather than instances, so they are introduced explicitly (`haveI`) before
  -- the transport: `Module.Projective.of_equiv` needs the source side in scope, and leaving
  -- it to synthesis fails.
  haveI := hc.finite_thetaGlued (A := A) a
  haveI := hc.projective_thetaGlued (A := A) a
  refine divisorWindow_eq_of_le_of_quotientData hH1 x
    (Module.Projective.of_equiv (windowQuotEquiv A hH1 hsurj).symm) (fun p => ?_) hle
  rw [congrFun (Module.rankAtStalk_eq_of_equiv (windowQuotEquiv A hH1 hsurj)) p]
  exact hc.rankAtStalk_thetaGlued a p

/-- **The window form at a CLASS rather than a local-equation system.**  `DivFam.window` is
`divisorWindow` of any representative's `eqns` (well defined by `divisorWindow_eq_of_divEq`),
so the same rank-engine argument applies verbatim with the class in place of `d`.

Stated separately from `divisorWindow_eq_of_le_of_quotientData` because the descent to a
representative is what a consumer must NOT do: unfolding `Quotient.lift` makes the window
elaborate through the section-ring algebra tower and exceeds the recursion limit.  Here the
quotient is never opened — `Submodule.eq_of_le_of_rankAtStalk_quotient_eq` is applied to
`F.window` directly, which is legitimate precisely because the engine is a statement about an
arbitrary pair of nested submodules. -/
theorem divisorWindowQuot_eq_of_le_of_quotientData {n : ℕ} (F : DivFam C R π n)
    (hH1 : Subsingleton (relTwistPair C k π (relThetaCocycle C k π a)).H1)
    (x : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) g R)
    (hproj : Module.Projective R
      ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸ F.window hH1))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk
        ((R ⊗[k] ↥(Scheme.divisorSections k (a • fiberWeilDivisor π) ⊤)) ⧸
          F.window hH1) p = g)
    (hle : x.toSubmodule ≤ F.window hH1) :
    F.window hH1 = x.toSubmodule := by
  haveI := hproj
  refine (Submodule.eq_of_le_of_rankAtStalk_quotient_eq hle fun p => ?_).symm
  rw [x.rankAtStalk_eq p, hrank p]

end WindowQuot

/-! ## Base-changed Grassmannian submodules -/

/-- A mapped Grassmannian submodule fills any projective constant-rank quotient that contains
the base change of an ambient upper bound.  This is the base-change form of the rank engine:
the source containment is transported by monotonicity of `windowBaseChange`, and the target
containment becomes equality because both quotient ranks are `g`.

The conclusion is stated under the algebra structure induced by `alpha`, matching
`Module.Grassmannian.map` definitionally and avoiding transport between equal algebra instance
packs. -/
theorem Grassmannian.eq_map_toSubmodule_of_baseChange_le
    {H : Type u} [AddCommGroup H] [Module k H]
    {S T : Type u} [CommRing S] [Algebra k S] [CommRing T] [Algebra k T]
    {g : ℕ} (alpha : S →ₐ[k] T)
    (x : Grassmannian.grFunctorAff k H g S)
    (N : Submodule S (TensorProduct k S H))
    (K : Submodule T (TensorProduct k T H))
    (hx : x.toSubmodule ≤ N) :
    letI : Algebra S T := alpha.toAlgebra
    letI : IsScalarTower k S T :=
      .of_algebraMap_eq fun a => (alpha.commutes a).symm
    windowBaseChange T N ≤ K →
      Module.Projective T (TensorProduct k T H ⧸ K) →
      (∀ p : PrimeSpectrum T,
        Module.rankAtStalk (TensorProduct k T H ⧸ K) p = g) →
      K = (Module.Grassmannian.map alpha x).toSubmodule := by
  letI : Algebra S T := alpha.toAlgebra
  letI : IsScalarTower k S T :=
    .of_algebraMap_eq fun a => (alpha.commutes a).symm
  intro hpull hproj hrank
  letI : Module.Projective S (TensorProduct k S H ⧸ x.toSubmodule) :=
    x.projective_quotient
  have hmap : (Module.Grassmannian.map alpha x).toSubmodule =
      windowBaseChange T x.toSubmodule :=
    (Module.Grassmannian.map_toSubmodule alpha x).trans
      (windowBaseChange_eq_ker_baseChangeMkQ T x.toSubmodule).symm
  have hmono : windowBaseChange T x.toSubmodule ≤ windowBaseChange T N := by
    unfold windowBaseChange
    exact Submodule.map_mono (Submodule.baseChange_mono T hx)
  have hle : (Module.Grassmannian.map alpha x).toSubmodule ≤ K := by
    rw [hmap]
    exact hmono.trans hpull
  letI : Module.Projective T (TensorProduct k T H ⧸ K) := hproj
  refine (Submodule.eq_of_le_of_rankAtStalk_quotient_eq hle fun p => ?_).symm
  rw [(Module.Grassmannian.map alpha x).rankAtStalk_eq p, hrank p]

/-! ## The ε-pair, for an arbitrary class -/

section EpsQuot

-- the three curve instances below are consumed by `divFamEps_eq_of_le` (through the landed
-- `DivSchemeFrameCover` window-quotient lemmas) but NOT by the carrier-free theorems above it.
-- `omit`-ing them per-theorem is rejected (they are referenced elsewhere in the section), so the
-- unused-section-variable linter is disabled here rather than the section being split.
set_option linter.unusedSectionVars false
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hπ : π ≫ P1.structureMap k = C.left ↘ Spec (.of k))
variable {g : ℕ}

/-- **THE CARRIER-FREE ε-PAIR IDENTITY.**  For an *arbitrary* class `F : DivFam C R π g` —
no certificate threaded, no adaptation named — `ε` of `F` is the Grassmannian pair `(x₁, x₂)`
as soon as each `xᵢ` is contained in the corresponding window of `F` and each window quotient
is projective of constant rank `g`.

This is the form a producer on **either** carrier can feed: the chart-typed one through
`windowQuotEquiv` off its own certificate (see
`divisorWindow_eq_of_le_of_isCertified_of_quotientData`), and the widened R2 one through
whatever makes its glued module invertible — the statement does not care, because
`DivFam.window` is `divisorWindow` of a representative's `eqns` and `divisorWindow` reads
nothing else.

Read together with the module docstring: this is the half of U2 that
`forall_not_isCertified_of_straddling` does **not** refute. -/
theorem divFamEps_eq_of_le_of_quotientData (F : DivFam C R π g)
    (x₁ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) g R)
    (x₂ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) g R)
    (hproj₁ : Module.Projective R
      ((R ⊗[k] ↥(Scheme.divisorSections k
          (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
        F.window (relThetaPairH1_windowM C π hπ g)))
    (hrank₁ : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk
        ((R ⊗[k] ↥(Scheme.divisorSections k
            (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) ⧸
          F.window (relThetaPairH1_windowM C π hπ g)) p = g)
    (hproj₂ : Module.Projective R
      ((R ⊗[k] ↥(Scheme.divisorSections k
          ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
        F.window (relThetaPairH1_windowMS C π hπ g)))
    (hrank₂ : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk
        ((R ⊗[k] ↥(Scheme.divisorSections k
            ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) ⧸
          F.window (relThetaPairH1_windowMS C π hπ g)) p = g)
    (hle₁ : x₁.toSubmodule ≤ F.window (relThetaPairH1_windowM C π hπ g))
    (hle₂ : x₂.toSubmodule ≤ F.window (relThetaPairH1_windowMS C π hπ g)) :
    divFamEps hπ g F = (x₁.toSubmodule, x₂.toSubmodule) :=
  -- `divFamEps` is the pair of the two `DivFam.window`s BY DEFINITION (`divFamEps`,
  -- `Picard/DivisorFamilyWindow.lean`), so no `Quotient.ind` is needed: the two components
  -- are the two hypotheses' subjects on the nose.  Descending to a representative instead
  -- makes the window unfold through the section-ring algebra tower and blows the recursion
  -- limit -- measured, at exactly the two `Prod.ext` legs.
  Prod.ext
    (divisorWindowQuot_eq_of_le_of_quotientData F _ x₁ hproj₁ hrank₁ hle₁)
    (divisorWindowQuot_eq_of_le_of_quotientData F _ x₂ hproj₂ hrank₂ hle₂)

set_option maxHeartbeats 2000000 in
-- both landed window-quotient lemmas unfold `DivFam.window` through the section-ring algebra
-- tower at each of the two pinned ledger windows; this is the defeq profile the satisfiability
-- probe was measured at, and the default budget does not reach it
set_option synthInstance.maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
/-- **THE ε-PAIR IDENTITY FROM CONTAINMENT ALONE — the satisfiability probe, discharged.**

The module docstring says this file owes a satisfiability check: the window-quotient hypotheses
are *determined* by `F` rather than consumer-chosen, so the live failure mode is not vacuity but
**unsatisfiability** — a reduction to a false hypothesis passes every `sorry` census and axiom
probe, because it is then a theorem.

**The check comes back positive, and better than positive: the hypotheses are already landed,
unconditionally, on `DivFam`.**  `Picard/DivSchemeFrameCover.lean` carries
`DivFam.projective_window_quotient` and `DivFam.rankAtStalk_window_quotient` for *every*
`F : DivFam C R π g` at *every* window `a ≥ windowM_choice`, discharged inside from the
representative's own certificate — which `DivFam` has by construction, since
`CertifiedDivisorFamily` is a triple carrying one.

So at the two pinned ledger windows the ε-pair identity needs **only the two containments**:

* `hle₁` is DDR-3's `le_vanishingSubmodule` at the seed;
* `hle₂` is the named DDR-5 second-window boundary.

**What this does and does not settle.**  It settles that the ε-half of U2 is not a reduction to
a false hypothesis — the hypothesis holds for every `DivFam`, so it is satisfiable wherever a
`DivFam` exists.  It does **not** produce a `DivFam` over the chart ring: that is the class
half, and it remains the whole open obligation (protection `I-0492`'s widening is the route).

**The sharp reading, and it is a demotion of this file's own headline.**  If the window-quotient
facts were already unconditional on `DivFam`, then the ε-half of U2 was never gated on a
certificate *at all* — not even on the weakened `HasCertifiedAdaptation` of
`Picard/DivRepChartClassUnivAny.lean`.  What the earlier sessions read as "U2 needs a
certificate" was the **class** requirement leaking into the ε statement through the carrier:
you cannot *write* `divFamEps hπ g F` without an `F`, and every `F` carries a certificate.  The
ε layer never asked for one beyond that. -/
theorem divFamEps_eq_of_le (F : DivFam C R π g)
    (hπ' : π ≫ P1.structureMap k = C.hom)
    (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
    (hχ : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
    (x₁ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k (windowM_choice π hπ g • fiberWeilDivisor π) ⊤)) g R)
    (x₂ : Grassmannian.grFunctorAff k
      (↥(Scheme.divisorSections k
        ((windowM_choice π hπ g + windowS_choice π hπ g) • fiberWeilDivisor π) ⊤)) g R)
    (hle₁ : x₁.toSubmodule ≤ F.window (relThetaPairH1_windowM C π hπ g))
    (hle₂ : x₂.toSubmodule ≤ F.window (relThetaPairH1_windowMS C π hπ g)) :
    divFamEps hπ g F = (x₁.toSubmodule, x₂.toSubmodule) :=
  divFamEps_eq_of_le_of_quotientData hπ F x₁ x₂
    (DivFam.projective_window_quotient hπ' g hO hχ (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) le_rfl F)
    (DivFam.rankAtStalk_window_quotient hπ' g hO hχ (windowM_choice π hπ g)
      (relThetaPairH1_windowM C π hπ g) le_rfl F)
    (DivFam.projective_window_quotient hπ' g hO hχ
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) F)
    (DivFam.rankAtStalk_window_quotient hπ' g hO hχ
      (windowM_choice π hπ g + windowS_choice π hπ g)
      (relThetaPairH1_windowMS C π hπ g) (Nat.le_add_right _ _) F)
    hle₁ hle₂

end EpsQuot

end AlgebraicGeometry
