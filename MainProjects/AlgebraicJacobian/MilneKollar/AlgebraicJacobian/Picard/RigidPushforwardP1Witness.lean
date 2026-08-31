/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RigidPushforwardGammaBaseChange

/-!
# A curve that satisfies the B3 hypotheses: `ℙ¹` itself

`Picard/RigidPushforwardGammaBaseChange.lean` proves `Scheme.HasRigidPushforward C` for every
`C : Over (Spec k)` that is smooth of relative dimension one, proper and geometrically integral.
A theorem quantified over those three hypotheses is worth nothing if the tree contains no object
satisfying them, so this file exhibits one — the projective line over an arbitrary field — and
fires the gate at it (`hasRigidPushforward_p1Over`).

Two instances are needed, and neither is bookkeeping: both are named in the tree as *open*.

* **§1, geometric integrality.**  `Picard/RigidPushforwardP1Constants.lean`'s
  `p1TrivialConstants_of_proj` calls `GeometricallyIntegral (Proj ℤ[X₀,X₁] ⟶ ⊤_Scheme)` "the
  *whole* remaining B3-H0 frontier" and "a missing mathlib fact about `Proj`".  It follows in a
  dozen lines from material that landed after that docstring was written:
  `Adelic.instIsIntegralP1OverLeft` (`Picard/RigidPushforwardInstance.lean`) says `ℙ¹_K` is an
  integral scheme for **every** field `K`, which is exactly what geometric integrality of the
  integral model asks — the base scheme of the test square is terminal, so the test map `y` is
  `Subsingleton.elim`'d away and the test object is *isomorphic* to `(p1Over K).left`.

* **§2, smoothness of relative dimension one.**  Also unproduced before this file.  The two
  standard charts have polynomial section rings
  (`p1ChartSectionsAlgEquivX`/`Y`, `Picard/RigidPushforwardP1ChartSections.lean`), a polynomial
  ring in one variable is standard smooth of relative dimension one over its base (§2.1, via
  `SubmersivePresentation` with one generator and no relations), and the charts cover
  (`p1Chart_sup_eq_top`).

Together with the existing `Adelic.isProper_p1Over_hom` this discharges the whole hypothesis
bundle, so §3's `hasRigidPushforward_p1Over` is `inferInstance`.

## What this does and does not settle

It settles **non-vacuity**, and rather more than the minimum: `references/challenge.lean` states
the challenge's curve as exactly `[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
[GeometricallyIrreducible C.hom]` — there is **no** genus hypothesis there, `genus C` being a
`def` rather than a binder — so `ℙ¹` satisfies the challenge's *complete* curve bundle, and
`hasRigidPushforward_of_geometricallyIrreducible` below fires the gate at that bundle verbatim.
(`GeometricallyIrreducible` versus `GeometricallyIntegral` is bridged by
`Curve/GeometricallyReduced.lean`'s `Smooth.geometricallyIntegral`, which genuinely consumes the
smoothness binder; that is why `Picard/RigidPushforwardGammaBaseChange.lean` imports that file.)

What it does **not** settle is that the B3 headlines have ever been applied to concrete *data*.
Their remaining quantified hypothesis, `Scheme.Hom.FiberH1Vanishing L t`, has no producer
anywhere in the tree, so what is witnessed below is that the *curve* binders are satisfiable —
not that a specific `(L, h¹ = 0)` pair exists.  See the inbox note on the `h1Mod` bridge.

## On registering these as global instances

Inbox `I-0432` warns against registering a discharged gate as a global instance when an instance
*diamond* is live nearby, because a global instance fires inside every downstream statement and
that is exactly when the wrong branch of a diamond gets picked.  The warning does not bite here,
and the reason is structural rather than a survey: every class instantiated globally in this file
and in `Picard/RigidPushforwardGammaBaseChange.lean` — `Scheme.HasRigidPushforward`,
`SmoothOfRelativeDimension`, `GeometricallyIntegral`,
`Algebra.IsStandardSmoothOfRelativeDimension` — is **`Prop`-valued**, so any two instances of it
are equal by proof irrelevance and no choice of branch can change what a downstream statement
*means*.

The one data-valued instance in this file, the `k`-algebra structure on a chart section ring, is
exactly where a diamond *could* live, and it is `local` — re-declared verbatim from
`Picard/RigidPushforwardP1ChartSections.lean`, which in turn re-declares it verbatim from
`RiemannRoch/Adelic/P1ChartData.lean`.  That chain is why `p1ChartSectionsAlgEquivX` type-checks
against it: same term, not merely the same shape.

Sources: Stacks 01MZ (`Proj` of a graded ring), 00T2 (standard smooth ring maps); mathlib
`AlgebraicGeometry/AffineSpace.lean` has the affine analogue of §1.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Adelic

open Scheme Algebra AlgebraicGeometry.ProjectiveSpace

/-! ## §1. The integral model of the projective line is geometrically integral -/

open MvPolynomial in
/-- **`Proj ℤ[X₀, X₁] ⟶ ⊤_Scheme` is geometrically integral.**

`Picard/RigidPushforwardP1Constants.lean`'s §3b calls this "the *whole* remaining B3-H0
frontier": a single `k`-independent statement discharging `Γ(ℙ¹_k, 𝒪) = k` over every field at
once, and the projective analogue of mathlib's affine-space instances.

The proof is short because the hard half already landed.  A test square for geometric
integrality has the *terminal* scheme as its base, so the test map `y : Spec K ⟶ ⊤_Scheme` is
`Subsingleton.elim`'d to the canonical one and the test object `Z` is forced by
`IsPullback.isoIsPullback` to be isomorphic to `(p1Over K).left = ℙ¹_K`.  Integrality of that is
`Adelic.instIsIntegralP1OverLeft`, proved for an arbitrary field in
`Picard/RigidPushforwardInstance.lean`, and `IsIntegral` transports along an isomorphism. -/
instance instGeometricallyIntegralProjIntegralModel : GeometricallyIntegral
    (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)))) := by
  constructor
  intro K _ y Z fst snd hsq
  have hflip : IsPullback
      (pullback.snd (terminal.from (Spec (CommRingCat.of K)))
        (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)))))
      (pullback.fst (terminal.from (Spec (CommRingCat.of K)))
        (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)))))
      (terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))))
      (terminal.from (Spec (CommRingCat.of K))) :=
    (IsPullback.of_hasPullback _ _).flip
  have hy : y = terminal.from (Spec (CommRingCat.of K)) := Subsingleton.elim _ _
  subst hy
  have e : Z ≅ (p1Over K).left := hsq.isoIsPullback _ _ hflip
  haveI : IsIntegral ((p1Over K).left) := inferInstance
  exact IsIntegral.of_isIso e.inv

variable {k : Type u} [Field k]

/-- `ℙ¹_k ⟶ Spec k` is geometrically integral, for every field `k` — §1 fed to
`Adelic.geometricallyIntegral_p1Over`, which reduces it to the integral model because relative
projective space is by construction its base change. -/
instance instGeometricallyIntegralP1Over : GeometricallyIntegral ((p1Over k).hom) :=
  geometricallyIntegral_p1Over

/-! ## §2. The projective line is smooth of relative dimension one -/

/-! ### §2.1. A polynomial ring in one variable is standard smooth of relative dimension one -/

private noncomputable def unitPolynomialPresentation (R : Type u) [CommRing R] :
    SubmersivePresentation R (MvPolynomial Unit R ⧸ (Ideal.span <| Set.range
      (PEmpty.elim : PEmpty.{1} → MvPolynomial Unit R))) Unit PEmpty.{1} where
  __ := PreSubmersivePresentation.naive (v := (PEmpty.elim : PEmpty.{1} → MvPolynomial Unit R))
    PEmpty.elim (fun a b _ => by cases a)
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]; simp

private noncomputable def unitPolynomialQuotBotAlgEquiv (R : Type u) [CommRing R] :
    (MvPolynomial Unit R ⧸ (Ideal.span <| Set.range
      (PEmpty.elim : PEmpty.{1} → MvPolynomial Unit R))) ≃ₐ[R] MvPolynomial Unit R := by
  have hb : (Ideal.span <| Set.range
      (PEmpty.elim : PEmpty.{1} → MvPolynomial Unit R)) = ⊥ := by simp
  exact AlgEquiv.ofRingEquiv
    (f := (Ideal.quotEquivOfEq hb).trans (RingEquiv.quotientBot (MvPolynomial Unit R)))
    (fun _ => rfl)

/-- `MvPolynomial Unit R` is standard smooth of relative dimension one over `R`: the naive
presentation with one generator, no relations, and an empty Jacobian matrix (determinant `1`). -/
instance instIsStandardSmoothOfRelativeDimensionOneMvPolynomialUnit (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial Unit R) := by
  refine ⟨Unit, PEmpty.{1}, inferInstance, inferInstance,
    ⟨(unitPolynomialPresentation R).ofAlgEquiv (unitPolynomialQuotBotAlgEquiv R), ?_⟩⟩
  simp [Algebra.Presentation.dimension]

/-- `R[T]` is standard smooth of relative dimension one over `R`. -/
instance instIsStandardSmoothOfRelativeDimensionOnePolynomial (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (MvPolynomial.uniqueAlgEquiv R Unit)

/-! ### §2.2. The chart section rings, and the conclusion -/

section Charts

open Opposite

/-- The `k`-algebra structure on a chart section ring of `ℙ¹_k`, as an `Over (Spec k)` object.
Local to this section: it is the structure `p1ChartSectionsAlgEquivX`/`Y` are stated for. -/
noncomputable local instance instAlgebraP1ChartSections (i : ULift.{u} (Fin 2)) :
    Algebra k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) :=
  Scheme.toModuleKSheaf.algebraSection
    (Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (op (p1Chart k i))

/-- Each standard chart ring of `ℙ¹_k` is standard smooth of relative dimension one over `k` —
it *is* `k[T]` (`Picard/RigidPushforwardP1ChartSections.lean`), and §2.1 applies.

`local`, deliberately: its statement mentions the `local` algebra structure above, so a global
instance here would export a term that nothing downstream could re-derive. -/
local instance instIsStandardSmoothOfRelativeDimensionOneP1ChartSections
    (i : ULift.{u} (Fin 2)) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k
      Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) := by
  have e : Polynomial k ≃ₐ[k]
      Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i) := by
    obtain ⟨i⟩ := i
    match i with
    | 0 => exact (p1ChartSectionsAlgEquivX k).symm
    | 1 => exact (p1ChartSectionsAlgEquivY k).symm
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1) e

/-- **`ℙ¹_k ⟶ Spec k` is smooth of relative dimension one.**  Witness the affine pair
`(⊤, p1Chart k i)` at each point: the two charts cover (`p1Chart_sup_eq_top`), and on each the
structural ring map factors as `Γ(Spec k, ⊤) ≅ k → Γ(ℙ¹_k, Vᵢ)` (`algebraMap_p1ChartSections`),
which is standard smooth of relative dimension one by the previous instance. -/
instance instSmoothOfRelativeDimensionOneP1OverHom : SmoothOfRelativeDimension 1
    (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) := by
  constructor
  intro x
  have hcov : x ∈ (p1Chart k ⟨0⟩ ⊔ p1Chart k ⟨1⟩ :
      (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k))).Opens) := by
    rw [p1Chart_sup_eq_top]; trivial
  obtain ⟨i, hxi⟩ : ∃ i : ULift.{u} (Fin 2), x ∈ p1Chart k i := by
    rcases hcov with h | h
    · exact ⟨⟨0⟩, h⟩
    · exact ⟨⟨1⟩, h⟩
  refine ⟨⊤, isAffineOpen_top _, p1Chart k i, isAffineOpen_p1Chart k i, hxi, le_top, ?_⟩
  have hcomp : ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)).appLE ⊤ (p1Chart k i) le_top).hom
      = (algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i)).comp
        ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toRingHom) := by
    ext z
    change ((ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)).appLE ⊤ (p1Chart k i) le_top).hom z
      = algebraMap k Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k i)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv z)
    rw [algebraMap_p1ChartSections k i _]
    congr 1
    exact ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm_apply_apply z).symm
  rw [hcomp]
  refine RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _ _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr inferInstance

end Charts

/-- `ℙ¹_k ⟶ Spec k` is smooth of relative dimension one, at the `p1Over` spelling the B3
statements use.  (Instance search does not unfold `(p1Over k).hom` to the structural map of
relative projective space, so the restatement is needed.) -/
instance instSmoothOfRelativeDimensionOneP1Over :
    SmoothOfRelativeDimension 1 ((p1Over k).hom) :=
  instSmoothOfRelativeDimensionOneP1OverHom

/-! ## §3. The witness -/

/-- **The B3 gate is not vacuous: `ℙ¹_k` satisfies all three of its hypotheses.**

`Adelic.isProper_p1Over_hom` gives properness, §1 gives geometric integrality and §2 smoothness
of relative dimension one, so `Adelic.instHasRigidPushforwardOfCurve` fires by `inferInstance`.

The `#print axioms` of this theorem is `[propext, Classical.choice, Quot.sound]`, so the whole
chain — chart rings are polynomial rings, `ℙ¹_k` is integral, the Čech `H⁰` engine, the affine
base-change square, the gate — is unconditional at a concrete curve. -/
theorem hasRigidPushforward_p1Over : Scheme.HasRigidPushforward (p1Over k) := inferInstance

/-- **The gate at the challenge's own hypothesis bundle.**  `references/challenge.lean` states
the curve with `GeometricallyIrreducible` where `Scheme.HasRigidPushforward`'s producer wants
`GeometricallyIntegral`.  The two agree for a smooth morphism —
`Curve/GeometricallyReduced.lean`'s `Smooth.geometricallyIntegral` — so the gate synthesizes
verbatim at the challenge's hypotheses.  This is a smoke test with no content of its own; it
exists so that a change to either bundle breaks the build rather than the reading. -/
theorem hasRigidPushforward_of_geometricallyIrreducible
    (C : Over (Spec (CommRingCat.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom] :
    Scheme.HasRigidPushforward C := inferInstance

/-- The B3 base-change headline with its *curve* binders discharged: for an invertible `L` on
`ℙ¹_A` with fibrewise `h¹ = 0`, the formation of `p_* L` commutes with every ring map `A → A'`.

Read the scope exactly.  This substitutes a concrete curve into
`Adelic.rigidPushforward_baseChange` and leaves `L`, `hL` and `h1` quantified; since
`Scheme.Hom.FiberH1Vanishing` has no producer in the tree, it is evidence that the headlines'
*curve* hypotheses are satisfiable, not that the headlines have been applied to concrete data. -/
theorem rigidPushforward_baseChange_p1Over
    (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (L : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L)
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t)
    (A' : Type u) [CommRing A'] (φ : A →+* A') :
    IsIso (pushforwardBaseChangeMap
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom φ))
      (pullback.snd (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) (Spec.map (CommRingCat.ofHom φ)))
      (pullback.fst (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) (Spec.map (CommRingCat.ofHom φ)))
      pullback.condition L) :=
  rigidPushforward_baseChange (p1Over k) A L hL h1 A' φ

end Adelic

end AlgebraicGeometry
