/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardP1ChartSections
import AlgebraicJacobian.Picard.RigidPushforwardP1Topology
import AlgebraicJacobian.Picard.RigidPushforwardRank
import AlgebraicJacobian.Picard.RigidPushforwardAffineDescent
import AlgebraicJacobian.Picard.RigidPushforwardFrontier

/-!
# The `HasRigidPushforward` gate: the `locallyFree` half, unconditionally

`Picard/RigidPushforwardGate.lean` factored the B3 campaign gate
`Scheme.HasRigidPushforward` into four named leaves, and
`Picard/RigidPushforwardFrontier.lean` recorded the state after two of them
were discharged: three statements remained — integrality of `ℙ¹_k`, the rank
identity, and the `baseChange` field.

**Two of those three are now theorems, and this file assembles them.**

## What is closed

* **`IsIntegral (ℙ¹_k)`** (`instIsIntegralP1OverLeft` below).  The frontier
  file recorded this as "genuine missing mathematics": mathlib v4.31 has
  `GeometricallyIrreducible`/`Reduced`/`Integral` for *affine* space and no
  integrality API for `Proj` at all.  It is now unconditional, in two steps.

  `Picard/RigidPushforwardP1ChartSections.lean` identifies the standard chart
  section rings as polynomial rings,
  `Γ(ℙ¹_k, D₊(Xᵢ)) ≃ₐ[k] k[T]`.  The tree already had the *spanning* half
  (`span_pow_p1XSection_scaffold`, `RiemannRoch/Adelic/P1ChartData.lean` — the
  chart ring is the `k`-span of the powers of the chart coordinate, i.e. the
  evaluation `k[T] → Γ(V₀)` is surjective).  What was missing was injectivity,
  and it comes from the section-ring pushout: `V₀` is the fibre product of the
  affine `D₊(X₀) ⊆ Proj ℤ[X₀, X₁]` with `Spec k` over the terminal scheme, so
  mathlib's `isIso_pushoutSection_of_isAffineOpen` presents `Γ(V₀)` as a
  `CommRingCat` pushout, and `IsPushout.desc` against
  `(ℤ[T] → k[T], k → k[T])` produces a retraction.  A surjection with a
  retraction is bijective.  The `ℤ[T]` input is
  `Picard/RigidPushforwardP1ChartRing.lean`'s `p1AwayAlgEquiv`, the same
  dehomogenisation argument over an arbitrary commutative base ring.

  `Picard/RigidPushforwardP1Topology.lean` turns "both chart rings are
  domains" into integrality: reducedness by `IsReduced.of_openCover`, and
  irreducibility because the (nonempty) overlap is a dense irreducible subset
  of each chart, hence of their union.

* **`P1RankIdentity k A`** (`Picard/RigidPushforwardRank.lean`,
  `p1RankIdentity_proved`), for *every* `k`-algebra `A` — the `FiniteType`
  hypothesis the gate quantifies over is not needed.

Consequently `P1RigidPushforwardStatement k A` and, for an AJC curve, the
gate's whole `locallyFree` field are unconditional theorems
(`p1RigidPushforwardStatement_proved`, `rigidPushforwardLocallyFree_proved`).

## What remained — one statement, and it is now proved

**STATUS: nothing remains.**  The statement isolated below,
`RigidPushforwardGammaBaseChange C A`, is
`Adelic.rigidPushforwardGammaBaseChange_proved`
(`Picard/RigidPushforwardGammaBaseChange.lean`), and the gate is the global
instance `Adelic.instHasRigidPushforwardOfCurve` there.  What follows is the
record of the last reduction, not a survey of open work.

The gate's second field, `Scheme.RigidPushforwardBaseChange C A`.
`Picard/RigidPushforwardAffineDescent.lean` reduces it — by affine-target
descent, both sides of the adjunction mate being quasi-coherent on the affine
`Spec A'` — to the single module-level statement
`RigidPushforwardGammaBaseChange C A`: bijectivity of the canonical
`Γ(Spec A', ⊤) ⊗_{Γ(Spec A, ⊤)} Γ(C_A, L) → Γ(C_{A'}, g'^* L)`.  That is the
classical `H⁰`-base-change fact, and it is proved in
`Picard/RigidPushforwardGammaBaseChange.lean` from the Čech purity of the same
ℙ¹ engine.  `hasRigidPushforward_of_gammaBaseChange` below was the honest
statement of the gate's cost at **one** statement, and is now the last
conditional link in a chain with no free ends.

Nothing *in this file* claims the gate itself: the instance lives downstream,
in `Picard/RigidPushforwardGammaBaseChange.lean` §3, where its one hypothesis
is discharged.

Sources: Mumford, *Abelian Varieties*, II §5; Stacks 00NX, 01I8, 01XJ, 02KG;
EGA III 7.9.9; Kleiman, *The Picard scheme* (FGA Explained), §5.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Adelic

open Scheme

variable {k : Type u} [Field k]

/-! ## §1. The projective line over a field is an integral scheme -/

/-- **`ℙ¹_k` is an integral scheme.**  Both standard charts have polynomial
section rings (`Picard/RigidPushforwardP1ChartSections.lean`), hence are
integral domains, and the charts genuinely overlap (`p1Chart_inf_ne_bot`); so
`ℙ¹_k` is reduced and irreducible (`Picard/RigidPushforwardP1Topology.lean`).

This is the `H⁰`-finiteness anchor of the B3 ℙ¹ engine, in the sharpest form
isolated in §5 of `Picard/RigidPushforwardP1Constants.lean`: it feeds
`finite_appTop_of_universallyClosed`, hence `Module.Finite k Γ(ℙ¹_k, 𝒪)`,
hence — by qcqs `H⁰` flat base change and Serre dévissage — the engine's
`hH0` at every finitely generated `k`-algebra. -/
instance instIsIntegralP1OverLeft : IsIntegral ((p1Over k).left) :=
  isIntegral_p1Over_left_of_isDomain_charts k inferInstance inferInstance
    (p1Chart_inf_ne_bot k)

/-! ## §2. The ℙ¹ engine statement, and the gate's `locallyFree` field -/

/-- **The pinned ℙ¹ engine statement is a theorem.**  `P1RigidPushforwardStatement k A`
(`Picard/RigidPushforward.lean`:663) held modulo two statements in
`Picard/RigidPushforwardFrontier.lean`; both are now proved, so it is
unconditional at every finitely generated `k`-algebra `A`. -/
theorem p1RigidPushforwardStatement_proved
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    P1RigidPushforwardStatement k A :=
  p1RigidPushforwardStatement_of_isIntegral_of_rank A (p1RankIdentity_proved A)

/-- **The gate's `locallyFree` field, unconditionally.**  For an AJC curve
`C/k` — smooth of relative dimension one, proper, geometrically integral — the
rigid pushforward of an invertible sheaf with vanishing fibrewise `h¹` is,
near every point of `Spec A`, free of rank `h⁰` of the fibre.

`HasFiniteMapToP1 C` is not a hypothesis: it synthesizes for an AJC curve, and
the finite-pushforward transfer package along `π_A : C_A ⟶ ℙ¹_A` is already
discharged in the tree (`Picard/RigidPushforwardTransfer.lean`). -/
theorem rigidPushforwardLocallyFree_proved
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    Scheme.RigidPushforwardLocallyFree C A :=
  rigidPushforwardLocallyFree_of_isIntegral_of_rank C A (p1RankIdentity_proved A)

/-! ## §3. The gate from its one remaining statement -/

/-- **The whole gate from a single statement.**  `HasRigidPushforward C`, for
an AJC curve, now needs exactly one input: the `Γ`-level base-change
bijectivity `RigidPushforwardGammaBaseChange C A` at every finitely generated
`k`-algebra `A`.

Compare `hasRigidPushforward_of_leaves` (`Picard/RigidPushforwardGate.lean`),
which needed four, and `hasRigidPushforward_of_isIntegral_of_rank_of_baseChange`
(`Picard/RigidPushforwardFrontier.lean`), which needed three.  The two ℙ¹
leaves are discharged here; the sheaf-level content of the fourth is discharged
by affine-target descent in `Picard/RigidPushforwardAffineDescent.lean`; what
is left is the classical statement that `H⁰` of the family commutes with
arbitrary base change, at the level of `Γ(Spec A, ⊤)`-modules.

The route to it, and the precise pieces still missing, are recorded in the
module docstring of `Picard/RigidPushforwardAffineDescent.lean`. -/
theorem hasRigidPushforward_of_gammaBaseChange
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (hΓ : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      RigidPushforwardGammaBaseChange C A) :
    Scheme.HasRigidPushforward C :=
  hasRigidPushforward_of_isIntegral_of_rank_of_baseChange C
    (fun A => p1RankIdentity_proved A)
    (fun A => rigidPushforwardBaseChange_of_gamma C A (hΓ A))

end Adelic

end AlgebraicGeometry
