/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardGate
import AlgebraicJacobian.Picard.RigidPushforwardFiberChart
import AlgebraicJacobian.Picard.RigidPushforwardP1Sheaf

/-!
# The `HasRigidPushforward` frontier after the fibre-chart and sheaf bricks

`Picard/RigidPushforwardGate.lean` factored the B3 campaign gate into four
named leaves.  Two of them have since been discharged, and this file records
the resulting state of the frontier — as Lean, not as prose.

## What is now closed

* **Leaf 2, `P1CechFibrewiseBridge k A`, is PROVED**
  (`p1CechFibrewiseBridge_proved` below, from
  `Adelic.p1_hfib_of_fiberH1Vanishing`,
  `Picard/RigidPushforwardFiberChart.lean`).  Fibrewise Čech
  `h¹`-vanishing of a finitely presented `M` on `ℙ¹_A` at every scheme point
  really does force the base-linear Čech differential to stay surjective
  after `⊗ κ(𝔪)` at every maximal ideal.  The proof runs Stacks 02KG in
  degree `0` on each affine chart of `ℙ¹_A` — the section-ring pushout on
  arbitrary compatible affine opens (`isPushout_appLE_of_isPullback'`,
  generalising the `f ⁻¹ᵁ V`-pinned form, which is unusable here because
  `p ⁻¹ᵁ ⊤ = ℙ¹_A` is not affine), the resulting chart comparison
  `κ(t) ⊗_{Γ(Spec A, ⊤)} Γ(M, W) ≅ Γ(M_t, W_t)` and its restriction
  naturality, the intertwining with the Čech differential, and the
  maximal-ideal-to-point package.

* **Leaf 3's sheaf half is PROVED**
  (`Adelic.p1PushforwardLocalFreenessBridge_of_rank`,
  `Picard/RigidPushforwardP1Sheaf.lean`): a quasi-coherent module on
  `Spec R` whose global sections are finite projective *is* free of rank
  `rankAtStalk` on a basic-open neighbourhood of any point
  (`exists_free_restrict_of_finite_projective_sections`), and
  `Γ(Spec A, p_* M)` really is `ker d`
  (`Adelic.pushforwardTop_linearEquiv_ker`).

## STATUS: this file is superseded — read it as history

All three items below have since been discharged or reduced.  The current
frontier is `Picard/RigidPushforwardInstance.lean`, where the gate is derived
from **one** statement rather than three.  What this file still supplies is the
conditional plumbing (`p1RigidPushforwardStatement_of_isIntegral_of_rank` and
friends), which the assembly consumes; only the survey below is out of date, and
it is kept because the shape of the reduction is worth reading.

## What remained at the time of writing — two statements plus one field

`p1RigidPushforwardStatement_of_isIntegral_of_rank` below shows that the ℙ¹
engine statement, hence the gate's `locallyFree` field, now needs exactly:

1. **`IsIntegral (ℙ¹_k)`** — integrality of the projective line over the one
   field `k`.  **Now PROVED** (`Adelic.instIsIntegralP1OverLeft`,
   `Picard/RigidPushforwardInstance.lean`), so the `[IsIntegral …]` binders in
   this file synthesize.  The diagnosis below was right about *where* the
   difficulty was and stale about *how much* of it the tree had.  The
   load-bearing sub-probe is indeed the chart-ring identification
   `Γ(ℙ¹, D₊(X₀)) ≅ R[T]`, of which the tree had only the spanning half
   (`span_p1CoordAway_pow_top`, `span_pow_p1XSection_scaffold`,
   `RiemannRoch/Adelic/P1ChartData.lean`), i.e. surjectivity of `R[T] → Γ(V₀)`;
   `RelLaurentChartData` likewise supplies spanning but never a basis.  The
   missing injectivity is now `Picard/RigidPushforwardP1ChartRing.lean`
   (`p1AwayAlgEquiv`, dehomogenisation over an arbitrary base ring) plus
   `Picard/RigidPushforwardP1ChartSections.lean` (the section-ring pushout
   supplies a retraction of the surjection), and
   `Picard/RigidPushforwardP1Topology.lean` transports it to `IsReduced` and
   `IrreducibleSpace`.  mathlib still has `GeometricallyIrreducible`/`Reduced`/
   `Integral` only for *affine* space and no integrality API for `Proj`.

2. **`P1RankIdentity k A`** — **now PROVED**, for *every* `k`-algebra `A` and
   with no `FiniteType` hypothesis (`Adelic.p1RankIdentity_proved`,
   `Picard/RigidPushforwardRank.lean`); the "assembly, not new mathematics"
   verdict below was right as mathematics and understated the Lean work by
   about a factor of three.  The statement: that the pointwise rank of `p_* M`
   really is
   the fibre `h⁰`, `sectionsRankAtStalk (p_* M) t = p.fiberH0 M t`, *for `M`
   satisfying the engine's own conclusions* (`d` surjective, `H⁰ = ker d`
   finite projective, `H⁰` base-change compatible).  Those hypotheses are
   load-bearing, not decoration: dropped, the statement is FALSE — take
   `A = k[x]` and `M = 𝒪/x`, where `Γ(ℙ¹_A, M) = k` is torsion so the stalk
   rank is the junk value `0`, while the fibre is `ℙ¹_k` with `M_t = 𝒪` and
   `fiberH0 M t = 1`.  Projectivity is exactly what excludes it.  With them,
   this is the same fibre-chart base change leaf 2 already uses: the chart
   comparison `exists_fiberChartTensorEquiv` identifies `ker (d ⊗ κ(t))` with
   the Čech `H⁰` of the fibre, i.e. with `Γ(ℙ¹_t, M_t)`, and
   `Module.rankAtStalk_eq` plus the engine's `kerBaseChange` bijectivity at
   `B = κ(t)` convert that into the rank statement.  So this is assembly of
   bricks that now exist, not new mathematics.

and, for the gate's second field,

3. **`Scheme.RigidPushforwardBaseChange C A`** — the only survivor, and now
   **REDUCED** rather than untouched: `Picard/RigidPushforwardAffineDescent.lean`
   descends it, along the affine target `Spec A'`, to the single module-level
   bijectivity `Adelic.RigidPushforwardGammaBaseChange C A`.  The diagnosis
   below is what made that possible and is still the right way to read the
   field.  Every `IsIso`
   theorem for the adjoint mate `pushforwardBaseChangeMap` in this tree
   requires `[IsAffineHom f]`, and `q : C_A ⟶ Spec A` is proper; with
   `IsAffineHom q` assumed the field closes in one line, so its entire
   content is the non-affine case.  There is also no composition/pasting API
   for `pushforwardBaseChangeMap`, so "reduce along the finite affine `π_A`,
   then treat `p : ℙ¹_A ⟶ Spec A`" cannot yet be assembled.

Sources: Mumford, *Abelian Varieties*, II §5; Stacks 02KG, 01YS; EGA III
7.9.9; Kleiman, *The Picard scheme* (FGA Explained), §5.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Adelic

open Scheme

variable {k : Type u} [Field k]

/-- **Leaf 2 of the gate is closed.**  `P1CechFibrewiseBridge k A` — fibrewise
Čech `h¹`-vanishing at all scheme points implies surjectivity of
`d ⊗ (Γ(Spec A, ⊤) ⧸ 𝔪)` at every maximal ideal — holds for every
`k`-algebra `A` (no finiteness on `A` needed).

This is `Adelic.p1_hfib_of_fiberH1Vanishing`
(`Picard/RigidPushforwardFiberChart.lean`) restated against the gate's pin. -/
theorem p1CechFibrewiseBridge_proved (A : Type u) [CommRing A] [Algebra k A] :
    P1CechFibrewiseBridge k A := by
  intro M hfp h1
  haveI := hfp
  exact p1_hfib_of_fiberH1Vanishing A M h1

/-- **The ℙ¹ engine statement from what actually remains.**  With leaf 2
proved and the sheaf half of leaf 3 proved, `P1RigidPushforwardStatement k A`
needs only

* `IsIntegral (ℙ¹_k)` (as an instance — the `H⁰`-finiteness anchor), and
* `P1RankIdentity k A`: the pointwise rank of `p_* M` is the fibre `h⁰`, for
  `M` satisfying the engine's conclusions (those hypotheses are necessary —
  see the module docstring for the counterexample without them).

`P1RankIdentity` is assembly of existing bricks; `IsIntegral (ℙ¹_k)` is the
genuine remaining mathematics. -/
theorem p1RigidPushforwardStatement_of_isIntegral_of_rank
    [IsIntegral ((p1Over k).left)]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hrank : P1RankIdentity k A) :
    P1RigidPushforwardStatement k A :=
  p1RigidPushforwardStatement_of_leaves_of_isIntegral A
    (p1CechFibrewiseBridge_proved A)
    (p1PushforwardLocalFreenessBridge_of_rank A hrank)

/-- **The gate's `locallyFree` field from what actually remains.**  For an AJC
curve, rank-`χ` local freeness of the rigid pushforward for the constant curve
`C_A` follows from `IsIntegral (ℙ¹_k)` and the rank identification alone —
`HasFiniteMapToP1 C` and the entire finite-pushforward transfer package along
`π_A : C_A ⟶ ℙ¹_A` are already discharged in the tree. -/
theorem rigidPushforwardLocallyFree_of_isIntegral_of_rank
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    [IsIntegral ((p1Over k).left)]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hrank : P1RankIdentity k A) :
    Scheme.RigidPushforwardLocallyFree C A :=
  rigidPushforwardLocallyFree_of_p1Engine A C
    (p1RigidPushforwardStatement_of_isIntegral_of_rank A hrank)

/-- **The gate itself, from what actually remains.**  Three statements:
integrality of `ℙ¹_k`, the rank identification at every finitely generated
`k`-algebra, and the base-change field.  Nothing else about the B3 engine is
open. -/
theorem hasRigidPushforward_of_isIntegral_of_rank_of_baseChange
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    [IsIntegral ((p1Over k).left)]
    (hrank : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      P1RankIdentity k A)
    (hBC : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      Scheme.RigidPushforwardBaseChange C A) :
    Scheme.HasRigidPushforward C :=
  hasRigidPushforward_of_p1Engine_of_baseChange C
    (fun A => p1RigidPushforwardStatement_of_isIntegral_of_rank A (hrank A)) hBC

end Adelic

end AlgebraicGeometry
