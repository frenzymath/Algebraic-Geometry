/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardP1Constants
import AlgebraicJacobian.Picard.RigidPushforwardTransfer

/-!
# The `HasRigidPushforward` gate, factored into its exact remaining leaves

`Picard/RigidPushforward.lean` declares the campaign gate
`Scheme.HasRigidPushforward C` (:373) with two fields, `locallyFree` and
`baseChange`.  The purpose of this file was to make the *shape* of the
discharge exact: to say, as machine-checked Lean rather than prose, precisely
which statements remain and how they compose into the gate.

**STATUS: all four leaves are now closed and the gate has a producer**
(`Adelic.instHasRigidPushforwardOfCurve`,
`Picard/RigidPushforwardGammaBaseChange.lean`).  Read this file as the record
of the factorization — its conditional plumbing is still consumed — but not as
a survey of open work.

## The factorization

For an AJC curve — `C : Over (Spec k)` with
`[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]`
— the gate is *equivalent* to four named statements, three of which concern
only `ℙ¹`:

1. **`IsIntegral (ℙ¹_k)`** (`Picard/RigidPushforwardP1Constants.lean` §5):
   integrality of the projective line over the one field `k`.  This is the
   cheapest sufficient form of the `H⁰`-finiteness anchor.
   `GeometricallyIntegral (p1Over k).hom` is strictly stronger and implies it;
   `Γ(ℙ¹_k, 𝒪) = k` (`P1HasTrivialConstants k`, §3 there) is *incomparable*
   with it but also discharges the anchor, through
   `p1RigidPushforwardStatement_of_leaves`.
2. **`P1CechFibrewiseBridge k A`** (§1 here): fibrewise `Ȟ¹`-vanishing of `M`
   on `ℙ¹_A` at all scheme points forces the base-linear Čech differential to
   stay surjective after `⊗ κ(𝔪)` at maximal ideals.  This is the geometric
   half of Mumford's "vanishing on the closed fibres" hypothesis, in the
   spelling the algebraic engine consumes.
3. **`P1PushforwardLocalFreenessBridge k A`** (§2 here): the *output* bridge —
   the engine's module-level conclusion (`d` surjective, `H⁰ = ker d` finite
   projective, `H⁰` commuting with arbitrary base change) upgraded to the
   sheaf-level conclusion that `p_* M` is locally free of pointwise rank
   `p.fiberH0 M t`.
4. **`Scheme.RigidPushforwardBaseChange C A`** — the second gate field, for
   which the tree currently has *no* infrastructure at all (see the caveat
   below).  These four are named leaves, not equal-sized ones: leaf 4 is one
   of the gate's two fields and is plausibly larger than leaves 1–3 combined.

§3 assembles 1–3 into `P1RigidPushforwardStatement k A`, the sole hypothesis
of `rigidPushforwardLocallyFree_of_p1Engine`
(`Picard/RigidPushforwardTransfer.lean`:1391), hence into the gate's
`locallyFree` field; §4 assembles everything into `HasRigidPushforward C`.
Note that `HasFiniteMapToP1 C`, which the transfer package needs, is **not** a
leaf: it synthesizes for an AJC curve through
`hasFiniteMapToP1_of_existsNonconstantMapToP1` ∘
`existsNonconstantMapToP1_of_existsNonconstantMapToProjInt` ∘
`existsNonconstantMapToProjInt_of_ajc`
(`RiemannRoch/Adelic/{FiniteMapToP1,NonconstantToP1}.lean`), all sorry-free.

## Caveat on the `baseChange` field (recorded, not hidden)

`Scheme.RigidPushforwardBaseChange` asks for `IsIso` of the adjoint mate
`pushforwardBaseChangeMap` for the **proper** family `q : C_A ⟶ Spec A` and
*arbitrary* ring maps `A → A'`.  The tree's only `IsIso` theorems for that
mate (`isIso_pushforwardBaseChangeMap_of_isPullback`,
`Picard/RigidPushforwardTransfer.lean`:1108, and its chart form :949) require
`[IsAffineHom f]`, and with `IsAffineHom q` assumed the field closes in one
line — so the entire content of the field is the non-affine case.  There is
also no composition/pasting API for `pushforwardBaseChangeMap` in the tree, so
the natural "reduce along the finite `π_A`, then treat `p : ℙ¹_A ⟶ Spec A`"
strategy cannot yet be assembled even once the second half exists.  The
module-level input is available (`kerBaseChange` bijective for *every*
`Γ(Spec A, ⊤)`-algebra, the fourth conclusion of
`p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`); the sheaf-level bridge is
not.  This is deliberately left as the fourth leaf rather than papered over.

Sources: Mumford, *Abelian Varieties*, II §5; EGA III 7.9.9; Hartshorne III
12.11; Kleiman, *The Picard scheme* (FGA Explained), §5; Stacks 02KG.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Adelic

open Scheme

variable {k : Type u} [Field k]

/-! ## §1. Leaf 2 — the fibrewise Čech bridge on `ℙ¹_A`

The engine `p1Cech_h0_baseChange_of_fibrewise_h1_vanishing`
(`Picard/RigidPushforwardP1Engine.lean`:1198) runs Nakayama over the maximal
ideals of `Γ(Spec A, ⊤)`, so it needs `H¹` vanishing in the form
"`d ⊗ (R₀ ⧸ 𝔪)` is surjective".  `P1RigidPushforwardStatement` supplies `H¹`
vanishing in the *geometric* form `Hom.FiberH1Vanishing` — vanishing of the
concrete Čech `Ȟ¹` of `M_t` on *some* 2-affine cover of the scheme-theoretic
fibre `ℙ¹_t`, at *every* scheme point `t`.  This `Prop` is exactly the
implication between the two. -/

/-- **Leaf 2 (the fibrewise bridge)**: on `ℙ¹_A`, fibrewise Čech
`h¹`-vanishing of a finitely presented `M` at every scheme point implies that
the base-linear Čech difference map of the standard 2-chart cover stays
surjective after tensoring with the residue field `R₀ ⧸ 𝔪` of every maximal
ideal.

Both directions of the mismatch are favourable: the hypothesis ranges over
*all* scheme points while the conclusion needs only the closed ones, and
cover-independence of the fibrewise `Ȟ¹` is already unconditional
(`Scheme.Hom.FiberH1Vanishing.surjective_moduleSectionDiff`,
`Cohomology/StructureSheafModuleK/QuasicoherentDegreeOneVanishing.lean`).
What remains is the chart-level base-change identification
`κ(t) ⊗_{Γ(Spec A, ⊤)} Γ(M, U_i) ≅ Γ(M_t, U_i^t)`, i.e. Stacks 02KG in
degree `0` on each affine chart of `ℙ¹_A`. -/
def P1CechFibrewiseBridge (k : Type u) [Field k]
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules),
    M.IsFinitePresentation →
    (∀ t : Spec (CommRingCat.of A),
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing M t) →
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    ∀ (m : Ideal Γ(Spec (CommRingCat.of A), ⊤)), m.IsMaximal →
      Function.Surjective
        (((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M).baseChange
          (Γ(Spec (CommRingCat.of A), ⊤) ⧸ m))

/-! ## §2. Leaf 3 — the output bridge (module conclusion ⟹ sheaf conclusion)

`p1Cech_h0_baseChange_of_fibrewise_h1_vanishing` ends at the level of
`Γ(Spec A, ⊤)`-modules: `H⁰ = ker d` is finite projective and its formation
commutes with arbitrary base change.  `P1RigidPushforwardStatement` asks
instead for the *sheaf* `p_* M` on `Spec A` to be locally free with the
pointwise rank `p.fiberH0 M t`.  The two are connected by
`AffineCoverMVSquare.globalSectionsEquivKerModuleSectionDiffBase`
(`Picard/RigidPushforwardP1Engine.lean`:287, `Γ(ℙ¹_A, M) ≃ₗ ker d`),
quasi-coherence of the pushforward (`pushforward_isQuasicoherent`,
`Picard/QuotScheme.lean`) and the standard "finite projective localizes to
free" argument; the rank identification is the `B = κ(t)` case of the
base-change conclusion. -/

/-- **Leaf 3 (the output bridge)**: on `ℙ¹_A`, the engine's module-level
conclusion for a finitely presented `M` — the base-linear Čech differential
`d` surjective, `H⁰ = ker d` a finite projective `Γ(Spec A, ⊤)`-module, and
the formation of `H⁰` commuting with arbitrary base change — implies the
geometric conclusion of `P1RigidPushforwardStatement`: every `t : Spec A` has
an open neighbourhood on which `p_* M` is free of rank `p.fiberH0 M t`.

This is pure sheaf-theoretic packaging (no new cohomology): `Γ(Spec A, p_* M)`
is `Γ(ℙ¹_A, M) ≅ ker d`, the pushforward is quasi-coherent, a finite
projective module over a commutative ring becomes free on a basic open
neighbourhood of any prime, and the rank there is the `κ(t)`-dimension of
`κ(t) ⊗ ker d ≅ ker (d ⊗ κ(t)) = Γ(ℙ¹_t, M_t)`, i.e. `p.fiberH0 M t`. -/
def P1PushforwardLocalFreenessBridge (k : Type u) [Field k]
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ (M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules),
    M.IsFinitePresentation →
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₁
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        (p1BaseChangeCoverSquare A).U₂
    letI := (pullback.snd (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).baseSectionsModule M
        ((p1BaseChangeCoverSquare A).U₁ ⊓ (p1BaseChangeCoverSquare A).U₂)
    Function.Surjective ⇑((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) →
    Module.Finite Γ(Spec (CommRingCat.of A), ⊤)
      (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) →
    Module.Projective Γ(Spec (CommRingCat.of A), ⊤)
      (LinearMap.ker ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
        (pullback.snd (p1Over k).hom
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M)) →
    (∀ (B : Type u) [CommRing B] [Algebra Γ(Spec (CommRingCat.of A), ⊤) B],
      Function.Bijective (AlgebraicJacobian.TwoTerm.kerBaseChange
        ((p1BaseChangeCoverSquare A).moduleSectionDiffBase
          (pullback.snd (p1Over k).hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M) B)) →
    ∀ t : Spec (CommRingCat.of A),
      ∃ U : (Spec (CommRingCat.of A)).Opens, t ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj
            ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M) ≅
          _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf)
            (ULift.{u} (Fin ((pullback.snd (p1Over k).hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 M t))))

/-! ## §3. The ℙ¹ engine statement from the three ℙ¹ leaves -/

set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the instance-heavy `letI` environment (fleet recipe).
/-- **`P1RigidPushforwardStatement` from its three leaves.**  The pinned ℙ¹
engine (`Picard/RigidPushforward.lean`:663) follows from

* `P1HasTrivialConstants k` — `Γ(ℙ¹_k, 𝒪) = k` (the `H⁰`-finiteness anchor,
  §3 of `Picard/RigidPushforwardP1Constants.lean`);
* `P1CechFibrewiseBridge k A` — leaf 2;
* `P1PushforwardLocalFreenessBridge k A` — leaf 3;

with everything else — the `A`-coefficient Laurent ladder for `H¹`, the Serre
dévissage for `H⁰`, the two-term finite replacement, Nakayama, purity of the
kernel — already proved in the tree. -/
theorem p1RigidPushforwardStatement_of_leaves
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hk : P1HasTrivialConstants k)
    (hfib : P1CechFibrewiseBridge k A)
    (hshape : P1PushforwardLocalFreenessBridge k A) :
    P1RigidPushforwardStatement k A := by
  intro M hfp hflat h1 t
  haveI := hfp
  obtain ⟨hsurj, hfin, hproj, hbc⟩ :=
    p1Cech_h0_baseChange_of_fibrewise_h1_vanishing_of_p1TrivialConstants A hk M hflat
      (hfib M hfp h1)
  exact hshape M hfp hsurj hfin hproj hbc t

set_option maxHeartbeats 800000 in
-- Heartbeat headroom for the instance-heavy `letI` environment (fleet recipe).
/-- **`P1RigidPushforwardStatement` from the sharpest form of leaf 1.**  Same
as `p1RigidPushforwardStatement_of_leaves`, with `Γ(ℙ¹_k, 𝒪) = k` replaced by
the strictly weaker `IsIntegral (ℙ¹_k)` (see §5 of
`Picard/RigidPushforwardP1Constants.lean`: the Serre-dévissage anchor needs
only *finiteness* of `Γ(ℙ¹_A, 𝒪)`, and over a proper integral scheme that is
mathlib's `finite_appTop_of_universallyClosed`). -/
theorem p1RigidPushforwardStatement_of_leaves_of_isIntegral
    [IsIntegral ((p1Over k).left)]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hfib : P1CechFibrewiseBridge k A)
    (hshape : P1PushforwardLocalFreenessBridge k A) :
    P1RigidPushforwardStatement k A := by
  intro M hfp hflat h1 t
  haveI := hfp
  obtain ⟨hsurj, hfin, hproj, hbc⟩ :=
    p1Cech_h0_baseChange_of_fibrewise_h1_vanishing_of_isIntegral A M hflat (hfib M hfp h1)
  exact hshape M hfp hsurj hfin hproj hbc t

/-! ## §4. The gate -/

/-- **The `locallyFree` field of the gate from the three ℙ¹ leaves.**  For an
AJC curve, `HasFiniteMapToP1 C` is automatic, so the finite-pushforward
transfer package (`rigidPushforwardLocallyFree_of_p1Engine`) turns the ℙ¹
engine into rank-`χ` local freeness for the constant curve `C_A`. -/
theorem rigidPushforwardLocallyFree_of_leaves
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hk : P1HasTrivialConstants k)
    (hfib : P1CechFibrewiseBridge k A)
    (hshape : P1PushforwardLocalFreenessBridge k A) :
    Scheme.RigidPushforwardLocallyFree C A :=
  rigidPushforwardLocallyFree_of_p1Engine A C
    (p1RigidPushforwardStatement_of_leaves A hk hfib hshape)

/-- **The gate, factored.**  For an AJC curve `C/k`, `HasRigidPushforward C`
follows from the ℙ¹ engine statement at every finitely generated `k`-algebra
together with the base-change field at every finitely generated `k`-algebra.
This is the honest statement of what remains: the `locallyFree` half is
`P1RigidPushforwardStatement`, the `baseChange` half is untouched. -/
theorem hasRigidPushforward_of_p1Engine_of_baseChange
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    (hP1 : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      P1RigidPushforwardStatement k A)
    (hBC : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      Scheme.RigidPushforwardBaseChange C A) :
    Scheme.HasRigidPushforward C where
  locallyFree A := rigidPushforwardLocallyFree_of_p1Engine A C (hP1 A)
  baseChange A := hBC A

/-- **The gate from the four named leaves.**  *This is no longer the frontier* —
it is the four-leaf factorization, kept because the factorization is what the
later assemblies are built on.  For the current cost of the gate see
`Adelic.hasRigidPushforward_of_gammaBaseChange`
(`Picard/RigidPushforwardInstance.lean`), which needs **one** hypothesis.

The four leaves, and what became of each:

* `Γ(ℙ¹_k, 𝒪) = k` (one statement, `k`-only, reducible to geometric
  integrality of `Proj ℤ[X₀, X₁]`) — superseded by the weaker
  `IsIntegral (ℙ¹_k)`, which is now **proved**
  (`Adelic.instIsIntegralP1OverLeft`);
* the fibrewise Čech bridge on `ℙ¹_A` (leaf 2) — **proved**
  (`Adelic.p1CechFibrewiseBridge_proved`);
* the local-freeness output bridge on `ℙ¹_A` (leaf 3) — **proved**, its sheaf
  half in `Picard/RigidPushforwardP1Sheaf.lean` and the rank identity in
  `Picard/RigidPushforwardRank.lean`;
* the base-change field for the proper family `C_A ⟶ Spec A` (leaf 4) — also
  **proved**: reduced by affine-target descent to a single module-level
  statement (`Picard/RigidPushforwardAffineDescent.lean`), which is
  `Adelic.rigidPushforwardGammaBaseChange_proved`
  (`Picard/RigidPushforwardGammaBaseChange.lean`).  The "no infrastructure
  yet" caveat in the module docstring above is history, and so is the "only
  one still open" reading of this list. -/
theorem hasRigidPushforward_of_leaves
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIntegral C.hom]
    [IsIntegral ((p1Over k).left)]
    (hfib : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      P1CechFibrewiseBridge k A)
    (hshape : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      P1PushforwardLocalFreenessBridge k A)
    (hBC : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
      Scheme.RigidPushforwardBaseChange C A) :
    Scheme.HasRigidPushforward C :=
  hasRigidPushforward_of_p1Engine_of_baseChange C
    (fun A => p1RigidPushforwardStatement_of_leaves_of_isIntegral A (hfib A) (hshape A)) hBC

end Adelic

end AlgebraicGeometry
