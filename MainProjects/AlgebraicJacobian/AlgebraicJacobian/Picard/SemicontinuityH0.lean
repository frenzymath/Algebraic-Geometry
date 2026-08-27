/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.RigidPushforward

/-!
# B5 — semicontinuity of the fibrewise `h⁰`, both directions

Campaign milestone **B5** (`informal/pic-representability-campaign.md`): for
the constant curve `C_A = C ×_k Spec A` over a finitely generated
`k`-algebra `A` and an invertible sheaf `L` on `C_A`, the loci

* `{t : Spec A | h⁰(C_t, L_t) ≤ n}` are **open**, and
* `{t : Spec A | n ≤ h⁰(C_t, L_t)}` are **closed**.

Sources: Hartshorne III 12.8 (semicontinuity); Mumford, *Abelian
Varieties*, II §5 (the rank-of-minors argument on the two-term finite free
complex — the same engine as B3, which is why the plan files B5 "with B3");
Kleiman, *The Picard scheme* (FGA Explained), §5.

## Statement audit (verdicts recorded BEFORE proving, per the campaign checklist)

* **Honesty at stated generality**: upper semicontinuity of
  `t ↦ h⁰(X_t, F_t)` holds for any proper flat family with `F` coherent and
  flat over a **noetherian** base (Hartshorne III 12.8).  Here `X = C_A` is
  proper flat over `Spec A` (base change of the proper smooth `C/k`; a
  `k`-scheme is automatically flat over the field `k`) and an invertible `L`
  is coherent and flat over the base, so the pinned statement is TRUE for
  every finitely generated `k`-algebra `A` — the same noetherian pin as B3;
  milestone B2 extends consumers to arbitrary affine bases.
* **"Both directions" collapse (discrepancy note vs the plan's phrasing)**:
  for the ℕ-valued function `t ↦ h⁰(t)`, the two B5 directions are exact
  set-theoretic complements: `{n ≤ h⁰} = {h⁰ ≤ n − 1}ᶜ` (and `{0 ≤ h⁰}` is
  everything).  So a SINGLE gated direction (openness of the sublevel sets)
  yields the closed direction by `IsOpen.isClosed_compl` — proved
  unconditionally below (`isClosed_setOf_le_fiberH0`).  The plan's remark
  "the closed direction feeds B6 — D3 only pinned the open direction" is
  thereby discharged for free once the gate is.
* **No `h¹`-hypothesis**: unlike B3, semicontinuity needs no cohomological
  vanishing — only properness/flatness/coherence.  The gate must NOT carry
  a `FiberH1Vanishing` hypothesis (it would silently weaken every B6/J1
  consumer, which apply B5 precisely where `h¹` is unknown).
* **Vocabulary**: `h⁰` is `Scheme.Hom.fiberH0`
  (`Picard/RigidPushforward.lean`), the `κ(t)`-dimension of `Γ(C_t, L_t)` —
  the same pin as B3's rank, so B3's local-freeness conclusion and B5's
  loci speak about the same function; **P2-interface TODO** as recorded
  there.

## Gate

`HasH0Semicontinuity C` (`HasPicScheme` pattern: `Prop` class, **no
instances** anywhere; discharged by the B3/B5 session via the minors of the
Mumford two-term complex, then deleted).  The closed direction and the
`n = 0` degenerate case are proved here, unconditionally, from the gate.

## Route status (2026-07-29) — the prescription above is REFUTED, read this first

"Discharged via the minors of the Mumford two-term complex" named
`rank_pushforward_eq_fiberH0` (`Picard/RigidPushforwardRank.lean`) as the
bridge.  That **cannot work** (measured, filed as I-0884): the bridge carries
`hproj`, which its own file proves load-bearing by counterexample, and finite
projectivity forces the fibre rank *locally constant* — strictly stronger than
the semicontinuity this gate asks for.  The prescription inverts the difficulty.

What is landed instead, all sorry-free and axiom-clean, none of it instantiating
this gate:

* `Ideal.isOpen_fiberRank_le` (`Picard/FiberRankSemicontinuity.lean`) — the
  fibre-rank sublevel locus is open over any commutative ring, no flatness, no
  noetherian hypothesis;
* `AlgebraicJacobian.TwoTerm.isOpen_finrank_ker_baseChange_le`
  (`Picard/TwoTermKernelSemicontinuity.lean`) — the engine: `dim H⁰` of a
  two-term complex `k : K → Aⁿ` with `K` finitely presented projective is upper
  semicontinuous.  Projectivity sits on `K`, where the replacement supplies it
  for free; the jumping comes from the cokernel;
* `AlgebraicGeometry.finrank_ker_moduleSectionDiffBase_baseChange_eq_fiberH0`
  (`Picard/FiberH0CechKernel.lean`) — `p.fiberH0 M t` *is* the dimension of the
  base-changed Čech kernel, with no base-change hypothesis.

**Two obligations stand between those and this gate**, and a lane taking it
should start from them rather than from the minors: (i) replacing the Čech
difference map by a complex of the engine's shape, where
`TwoTermFiniteReplacement.h0_bijective` is the residual content, and (ii) the
carrier transport across `Scheme.ΓSpecIso` between a bare ring's
`PrimeSpectrum` and `Γ(Spec R, ⊤)`.  See
`Picard/FiberH0Comparison.lean`'s corrected obligation list.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k]

/-- **B5 statement pin (open direction)**: for every invertible sheaf `L` on
`C_A` and every `n`, the sublevel locus `{t : Spec A | h⁰(C_t, L_t) ≤ n}`
is open — upper semicontinuity of the fibrewise `h⁰`
(Hartshorne III 12.8; Mumford AV II §5 minors-of-the-complex argument).
Honestly TRUE for `A` a finitely generated `k`-algebra (noetherian pin —
see the module docstring audit); the gate `HasH0Semicontinuity` quantifies
it exactly there. -/
def H0UpperSemicontinuity (C : Over (Spec (CommRingCat.of k)))
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules,
    LineBundle.IsLocallyTrivial L →
    ∀ n : ℕ, IsOpen {t : Spec (CommRingCat.of A) |
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t ≤ n}

/-- **The B5 gate** (`HasPicScheme` pattern: `Prop` class, **no instances
anywhere in the tree**; supplied as a hypothesis by consumers and discharged
by the B3/B5 session — the minors of the two-term finite free complex —
then deleted).  Content: `h⁰` upper semicontinuity over every finitely
generated `k`-algebra base.  The closed direction is NOT a separate field:
it is the set-theoretic complement, proved below
(`isClosed_setOf_le_fiberH0`). -/
class HasH0Semicontinuity (C : Over (Spec (CommRingCat.of k))) : Prop where
  /-- `h⁰` upper semicontinuity over every finitely generated `k`-algebra. -/
  upperSemicontinuity : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
    H0UpperSemicontinuity C A

variable (C : Over (Spec (CommRingCat.of k)))
variable (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- **B5, open direction** (extraction from the gate): `{h⁰(L_t) ≤ n}` is
open in `Spec A`. -/
theorem isOpen_setOf_fiberH0_le [HasH0Semicontinuity C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) (n : ℕ) :
    IsOpen {t : Spec (CommRingCat.of A) |
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t ≤ n} :=
  HasH0Semicontinuity.upperSemicontinuity A L hL n

/-- **B5, closed direction** (proved from the gate — the plan's "both
directions" collapse to complements for the ℕ-valued `h⁰`, see the module
docstring): `{n ≤ h⁰(L_t)}` is closed in `Spec A`.  This is the direction
milestone B6 consumes (closedness of the triviality locus
`{h⁰(L_t) ≥ 1} ∩ {h⁰(L_t⁻¹) ≥ 1}` in fibre degree 0). -/
theorem isClosed_setOf_le_fiberH0 [HasH0Semicontinuity C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L) (n : ℕ) :
    IsClosed {t : Spec (CommRingCat.of A) |
      n ≤ (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t} := by
  cases n with
  | zero =>
    have huniv : {t : Spec (CommRingCat.of A) |
        0 ≤ (pullback.snd C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t} = Set.univ :=
      Set.eq_univ_of_forall fun t => Nat.zero_le _
    rw [huniv]
    exact isClosed_univ
  | succ m =>
    have hcompl : {t : Spec (CommRingCat.of A) |
        m + 1 ≤ (pullback.snd C.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t} =
        {t : Spec (CommRingCat.of A) |
          (pullback.snd C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t ≤ m}ᶜ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
      exact Nat.lt_iff_add_one_le.symm
    rw [hcompl]
    exact (isOpen_setOf_fiberH0_le C A L hL m).isClosed_compl

end Scheme

end AlgebraicGeometry
