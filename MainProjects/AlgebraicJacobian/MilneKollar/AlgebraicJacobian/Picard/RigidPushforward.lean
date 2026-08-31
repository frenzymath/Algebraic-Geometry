/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Picard.HilbertPolynomial
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.FlatteningStratification
import AlgebraicJacobian.Picard.GlueDescent
import AlgebraicJacobian.Cohomology.MayerVietorisCover
import AlgebraicJacobian.Cohomology.FlatBaseChange
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1

/-!
# B3 — the rigid pushforward engine: statement layer and ℙ¹ reduction skeleton

This file pins milestone **B3** of the Picard-representability campaign
(`informal/pic-representability-campaign.md`), the engine
`pushforward_locallyFree_of_h1_vanishing`: for the constant curve
`C_A = C ×_k Spec A` over a finitely generated `k`-algebra `A` and an
invertible sheaf `L` on `C_A` with `h¹(C_t, L_t) = 0` at **every scheme
point** `t : Spec A`, the pushforward `q_* L` along `q : C_A ⟶ Spec A` is
locally free with fibre rank `h⁰(C_t, L_t) (= χ(L_t))`, and its formation
commutes with **arbitrary** ring maps `A → A'`.

Sources: Mumford, *Abelian Varieties*, II §5 (the two-term finite free
complex and "cohomology and base change"); EGA III 7.9.9; Hartshorne III
12.11; Kleiman, *The Picard scheme* (FGA Explained), §5 — B3 is the engine
behind Kleiman's flattening/openness arguments in the curve case.

## Statement audit (campaign checklist item 1 — BLOCKING; verdicts recorded here)

* **Quantifier — `h¹ = 0` at ALL scheme points** (`RigidPushforwardLocallyFree`,
  `RigidPushforwardBaseChange`): the hypothesis `∀ t : Spec A,
  q.FiberH1Vanishing L t` ranges over *all* points of the underlying space of
  `Spec A` (all primes), not only closed points.  For general noetherian `A`
  (noetherian ≠ Jacobson: e.g. a DVR, whose generic point is contained in no
  closed point's closure) the closed-point form is strictly weaker and the
  engine's conclusion FAILS if the hypothesis is checked at closed points
  only.  A finitely generated `k`-algebra *is* Jacobson, so on the pinned
  base the two forms happen to agree — but (i) the reduction uses h¹ upper
  semicontinuity, an engine we refuse to smuggle into the *statement*, and
  (ii) milestone B2 extends every consumer along filtered colimits and
  localizations, where the base is merely noetherian and Jacobson genuinely
  fails.  All campaign consumers (J1/J3 `h⁰ ≡ 1`, B4–B6) supply the
  hypothesis at all scheme points anyway.  VERDICT: pin at all scheme points.
* **Base change along ARBITRARY `A → A'` in the statement**
  (`RigidPushforwardBaseChange`): quantified over every commutative ring
  `A' : Type u` and every ring hom `φ : A →+* A'` — no finiteness, no
  flatness, no noetherian hypothesis on `A'`.  The comparison morphism is
  the canonical `pushforwardBaseChangeMap` (Stacks 02N4-style mate) of the
  *defining pullback square* of `q` along `Spec φ`, so the statement is
  well-formed with zero transport: the base-changed family is
  `pullback q (Spec.map φ)` — canonically (but not definitionally) isomorphic
  to `C ×_k Spec A'`; the comparison iso is postponed to the consumer layer
  (B2), keeping the pin transport-free.  VERDICT: arbitrary `A'`, arbitrary
  `φ`, canonical square, comparison map in the statement.
* **Two-step pin**: step 1 = rank-`χ` local freeness
  (`RigidPushforwardLocallyFree`) + base change
  (`RigidPushforwardBaseChange`); step 2 = the rank-one corollary
  (`pushforward_isLocallyTrivial_of_h1_vanishing`, proved from the gate).
  VERDICT: pinned as two separate `Prop`s consumed by one gate.
* **Rank = `χ(L_t)`** : under `h¹(L_t) = 0` we have `χ(L_t) = h⁰(L_t)`, and
  `h⁰` *is* expressible today (`Scheme.Hom.fiberH0`, the `κ(t)`-dimension of
  `Γ(C_t, L_t)`, matching `Scheme.hilbertFunction`'s convention), while the
  `χ`-ledger is milestone P3.  The rank is therefore pinned as
  `q.fiberH0 L t`; **P2/P3-interface TODO**: once the P2 cohomology kit and
  the P3 `χ`-ledger land, add the (definitionally compatible) reformulation
  `rank = χ(L_t) = deg L_t + 1 - g`.
* **Fibrewise `h¹` vocabulary** (P2 does not exist yet): the hypothesis is
  pinned in the weakest honest form the adelic lane can already express —
  existence of a 2-affine Čech cover (`AffineCoverMVSquare`, the lane's
  carrier) of the scheme-theoretic fibre on which the degree-1 Čech
  cokernel of `L_t` vanishes, i.e. the difference-of-restrictions map is
  surjective (`Scheme.Hom.FiberH1Vanishing`; carrier form
  `AffineCoverMVSquare.moduleH1Cok`, mirroring
  `AffineCoverMVSquare.H1Cok` of `RiemannRoch/Adelic/Cokernel.lean`).  On a
  separated scheme with an affine 2-cover, this Čech `H¹` computes sheaf
  `H¹` for quasi-coherent modules (Mayer–Vietoris/Leray; in-lane precedent
  `hModuleOne_linearEquiv_cechCohomology`), and any two such covers agree —
  cover-independence is exactly the **P2-interface TODO**, to be discharged
  Čech-to-Čech.  The ∃-form is chosen because it is *implied* by every
  future kit form, so the gate only gets easier to discharge.
* **The rank-one corollary's `DivFamily` leg** (Kleiman §5; campaign J2):
  `h⁰ ≡ 1, h¹ ≡ 0 ⟹ q_*L` invertible is pinned and proved from the gate
  below.  The continuation — the counit section `q^*q_*L ⟶ L` is fibrewise
  nonzero, hence a regular section on the integral fibres, hence cuts a
  canonical `DivFamily` — needs the counit/adjunction vocabulary on the
  `Div` side and the geometric integrality of fibres; it is recorded as the
  **J2-interface TODO** and deliberately NOT pinned here (its natural home
  is the J2 session, where the target `DivFamily` shape is fixed).

## Gate

`HasRigidPushforward C` is the campaign gate (`HasPicScheme` pattern): a
`Prop` class carrying the two statement `Prop`s quantified over all finitely
generated `k`-algebras.  **It is now DISCHARGED**, by the Mumford two-term
complex route as planned: `Adelic.instHasRigidPushforwardOfCurve`
(`Picard/RigidPushforwardGammaBaseChange.lean`) is a global instance for an
AJC curve, and `Adelic.hasRigidPushforward_p1Over`
(`Picard/RigidPushforwardP1Witness.lean`) fires it at `ℙ¹`.  The class is
*kept* rather than deleted, so that consumers read as hypotheses on the
curve rather than on an opaque conjunction.  Everything else in this file is
*proved*: the
extraction theorems, the rank-one corollary, and the ℙ¹ reduction skeleton
(the base-changed finite map `C_A ⟶ ℙ¹_A`, the pushforward factorization
`q_* = p_* ∘ π_*`, and the reduction of B3-for-`C_A` to a ℙ¹ engine plus a
named finite-pushforward transfer package).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. Degree-1 Čech vocabulary for 𝒪-modules on a 2-affine cover

The adelic lane (`RiemannRoch/Adelic/Cokernel.lean`) works with sheaves of
`k`-modules; the Picard lane works with `X.Modules`.  The following is the
`X.Modules` dialect of the lane's `sectionDiff`/`H1Cok`/`sectionGlue` kit on
a bundled 2-affine cover (`AffineCoverMVSquare`).  Restriction maps of a
sheaf of modules are only *semilinear* over the restriction of scalars, so
the natural home of the difference map is additive homs. -/

variable {X S : Scheme.{u}}

/-- The **difference-of-restrictions map** of a 2-affine cover for a sheaf of
`𝒪_X`-modules `M`: the additive map
`Γ(U₁, M) × Γ(U₂, M) →+ Γ(U₁ ⊓ U₂, M)`, `(a, b) ↦ a|_{U₁⊓U₂} − b|_{U₁⊓U₂}`.
Its cokernel is the concrete Čech `Ȟ¹(𝒰, M)` of the cover
(`AffineCoverMVSquare.moduleH1Cok`), its kernel the glued global sections.
`X.Modules`-dialect of `AffineCoverMVSquare.sectionDiff`
(`RiemannRoch/Adelic/Cokernel.lean`). -/
noncomputable def AffineCoverMVSquare.moduleSectionDiff (V : X.AffineCoverMVSquare)
    (M : X.Modules) :
    Γ(M, V.U₁) × Γ(M, V.U₂) →+ Γ(M, V.U₁ ⊓ V.U₂) :=
  ((M.presheaf.map (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom.comp
      (AddMonoidHom.fst _ _)) -
    ((M.presheaf.map (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom.comp
      (AddMonoidHom.snd _ _))

/-- The value of the difference map. -/
lemma AffineCoverMVSquare.moduleSectionDiff_apply (V : X.AffineCoverMVSquare)
    (M : X.Modules) (p : Γ(M, V.U₁) × Γ(M, V.U₂)) :
    V.moduleSectionDiff M p =
      (M.presheaf.map (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom p.1 -
        (M.presheaf.map (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom p.2 :=
  rfl

/-- **The concrete Čech `Ȟ¹` of a 2-affine cover, `X.Modules` dialect**: the
cokernel `Γ(U₁ ⊓ U₂, M) ⧸ im(Γ(U₁, M) × Γ(U₂, M))` of the
difference-of-restrictions map, as an abelian group.  For quasi-coherent `M`
on a separated scheme this computes sheaf `H¹(X, M)` (Mayer–Vietoris on the
affine 2-cover; in-lane precedent `hModuleOne_linearEquiv_cechCohomology`).
`X.Modules`-dialect of `AffineCoverMVSquare.H1Cok`. -/
noncomputable def AffineCoverMVSquare.moduleH1Cok (V : X.AffineCoverMVSquare)
    (M : X.Modules) : Type u :=
  Γ(M, V.U₁ ⊓ V.U₂) ⧸ (V.moduleSectionDiff M).range

noncomputable instance (V : X.AffineCoverMVSquare) (M : X.Modules) :
    AddCommGroup (V.moduleH1Cok M) :=
  inferInstanceAs (AddCommGroup (_ ⧸ (V.moduleSectionDiff M).range))

/-- Vanishing of the concrete Čech `Ȟ¹` is surjectivity of the difference map. -/
lemma AffineCoverMVSquare.subsingleton_moduleH1Cok_iff (V : X.AffineCoverMVSquare)
    (M : X.Modules) :
    Subsingleton (V.moduleH1Cok M) ↔
      Function.Surjective ⇑(V.moduleSectionDiff M) := by
  constructor
  · intro h c
    have hc : (QuotientAddGroup.mk c : V.moduleH1Cok M) = QuotientAddGroup.mk 0 :=
      h.elim _ _
    rw [QuotientAddGroup.eq] at hc
    obtain ⟨p, hp⟩ := hc
    refine ⟨-p, ?_⟩
    have : -(V.moduleSectionDiff M p) = c := by
      rw [hp]; abel
    simpa [map_neg] using this
  · intro h
    have hrange : (V.moduleSectionDiff M).range = ⊤ :=
      AddMonoidHom.range_eq_top.mpr h
    change Subsingleton (Γ(M, V.U₁ ⊓ V.U₂) ⧸ (V.moduleSectionDiff M).range)
    rw [hrange]
    exact QuotientAddGroup.subsingleton_quotient_top

/-- The **pair-of-restrictions map** `Γ(X, M) →+ Γ(U₁, M) × Γ(U₂, M)` of a
2-affine cover: the degree-0 piece of the two-term Čech complex.  Together
with `moduleSectionDiff` this is the explicit two-term complex
`0 → Γ(M) → Γ(U₁, M) × Γ(U₂, M) → Γ(U₁ ⊓ U₂, M) → Ȟ¹ → 0` of Mumford AV
II §5 (before the finite free replacement). -/
noncomputable def AffineCoverMVSquare.moduleSectionRes (V : X.AffineCoverMVSquare)
    (M : X.Modules) :
    Γ(M, (⊤ : X.Opens)) →+ Γ(M, V.U₁) × Γ(M, V.U₂) :=
  ((M.presheaf.map (homOfLE (le_top : V.U₁ ≤ ⊤)).op).hom).prod
    ((M.presheaf.map (homOfLE (le_top : V.U₂ ≤ ⊤)).op).hom)

/-- **The two-term Čech complex property**: the composite
`Γ(M) → Γ(U₁, M) × Γ(U₂, M) → Γ(U₁ ⊓ U₂, M)` vanishes — restrictions of a
global section along the two legs agree on the overlap (functoriality of the
presheaf and proof irrelevance of `≤` in `Opens`). -/
lemma AffineCoverMVSquare.moduleSectionDiff_comp_moduleSectionRes
    (V : X.AffineCoverMVSquare) (M : X.Modules) :
    (V.moduleSectionDiff M).comp (V.moduleSectionRes M) = 0 := by
  ext s
  have h₁ : (M.presheaf.map (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op).hom
        ((M.presheaf.map (homOfLE (le_top : V.U₁ ≤ ⊤)).op).hom s) =
      (M.presheaf.map (homOfLE (le_top : V.U₁ ⊓ V.U₂ ≤ ⊤)).op).hom s := by
    have := M.presheaf.map_comp (homOfLE (le_top : V.U₁ ≤ ⊤)).op
      (homOfLE (inf_le_left : V.U₁ ⊓ V.U₂ ≤ V.U₁)).op
    exact (congrArg (fun f => (ConcreteCategory.hom f) s) this.symm).trans rfl
  have h₂ : (M.presheaf.map (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op).hom
        ((M.presheaf.map (homOfLE (le_top : V.U₂ ≤ ⊤)).op).hom s) =
      (M.presheaf.map (homOfLE (le_top : V.U₁ ⊓ V.U₂ ≤ ⊤)).op).hom s := by
    have := M.presheaf.map_comp (homOfLE (le_top : V.U₂ ≤ ⊤)).op
      (homOfLE (inf_le_right : V.U₁ ⊓ V.U₂ ≤ V.U₂)).op
    exact (congrArg (fun f => (ConcreteCategory.hom f) s) this.symm).trans rfl
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    moduleSectionDiff_apply, moduleSectionRes, AddMonoidHom.prod_apply]
  rw [h₁, h₂, sub_self]

/-- **The preimage of a 2-affine cover square under an affine morphism**: for
`f : X ⟶ Y` affine and a bundled 2-affine cover of `Y`, the preimages of the
two charts form a 2-affine cover of `X` (affine morphisms pull affine opens
back to affine opens, `IsAffineOpen.preimage`; preimages preserve `⊓`, `⊔`,
`⊤` definitionally).  Generalizes `Adelic.LaurentChartData.pullbackSquare`
(which is the special case of a finite morphism) to arbitrary affine
morphisms — in particular to the affine projection `ℙ¹_A ⟶ ℙ¹_k`, giving
the standard 2-chart cover of `ℙ¹_A` (`Adelic.p1BaseChangeCoverSquare`). -/
noncomputable def AffineCoverMVSquare.preimage {Y : Scheme.{u}}
    (V : Y.AffineCoverMVSquare) (f : X ⟶ Y) [IsAffineHom f] :
    X.AffineCoverMVSquare where
  U₁ := f ⁻¹ᵁ V.U₁
  U₂ := f ⁻¹ᵁ V.U₂
  isAffineOpen_U₁ := V.isAffineOpen_U₁.preimage f
  isAffineOpen_U₂ := V.isAffineOpen_U₂.preimage f
  isAffineOpen_inf := V.isAffineOpen_inf.preimage f
  cover := by
    change f ⁻¹ᵁ (V.U₁ ⊔ V.U₂) = ⊤
    rw [V.cover]
    rfl

/-! ## §2. Fibrewise `h⁰` and `h¹`-vanishing for a family -/

/-- The **fibrewise `h⁰`** of a sheaf of modules `L` on the total space of a
family `q : X ⟶ S` at a point `t : S`: the dimension over the residue field
`κ(t)` of the global sections of the restriction `L_t` of `L` to the
scheme-theoretic fibre `X_t = q.fiber t`,

`h⁰(t) = dim_{κ(t)} Γ(X_t, L_t)`.

The `κ(t)`-structure is `Scheme.Hom.fiberSectionsModule` (restriction of
scalars along `κ(t) → Γ(X_t, 𝒪)`), exactly the convention of
`Scheme.hilbertFunction`; when the dimension is infinite, `Module.finrank`
takes the junk value `0`.  This is the (P2-kit-independent) fibre `h⁰`
vocabulary of campaign milestones B3/B5/B6/J1/J3. -/
noncomputable def Hom.fiberH0 (q : X ⟶ S) (L : X.Modules) (t : S) : ℕ :=
  letI := q.fiberSectionsModule t (q.fiberModule t L)
  Module.finrank (S.residueField t) Γ(q.fiberModule t L, (⊤ : (q.fiber t).Opens))

/-- **Fibrewise `h¹`-vanishing** of a sheaf of modules `L` on the total space
of a family `q : X ⟶ S` at a point `t : S`, in the weakest honest form the
adelic lane can express before the P2 cohomology kit exists: *some* 2-affine
Čech cover of the scheme-theoretic fibre `X_t = q.fiber t` has surjective
difference-of-restrictions map for `L_t` — equivalently (by
`AffineCoverMVSquare.subsingleton_moduleH1Cok_iff`) vanishing concrete Čech
`Ȟ¹(𝒰, L_t)`.

On the separated fibre curves of the campaign this Čech `Ȟ¹` computes sheaf
`H¹(X_t, L_t)` and is independent of the chosen 2-affine cover
(Mayer–Vietoris); the ∃-form is implied by every future P2-kit form of
`h¹ = 0`, so hypotheses pinned this way only get easier to supply.
Cover-independence Čech-to-Čech is the recorded **P2-interface TODO**. -/
def Hom.FiberH1Vanishing (q : X ⟶ S) (L : X.Modules) (t : S) : Prop :=
  ∃ V : (q.fiber t).AffineCoverMVSquare,
    Function.Surjective ⇑(V.moduleSectionDiff (q.fiberModule t L))

/-! ## §3. The B3 statement pins and the gate -/

variable {k : Type u} [Field k]

/-- **B3, step 1a (statement pin): rank-`χ` local freeness of the rigid
pushforward** (Mumford AV II §5, Corollary 2; EGA III 7.9.9; Hartshorne III
12.11; campaign milestone B3(i), first conclusion).

For the constant curve `C_A = C ×_k Spec A` with projection
`q = pullback.snd : C_A ⟶ Spec A` and every invertible sheaf `L` on `C_A`
with `h¹(C_t, L_t) = 0` at **every scheme point** `t : Spec A` (see the
module docstring for the quantifier audit), the pushforward `q_* L` is
locally free with stalkwise rank the fibre dimension
`h⁰(C_t, L_t) = χ(L_t)`: every point has an open neighbourhood `U` on which
`(q_* L)|_U ≅ 𝒪_U^{⊕ h⁰(t)}`.

The rank is pinned as `q.fiberH0 L t` (`= χ(L_t)` since `h¹ = 0`; the
`χ`-ledger reformulation is the P3-interface TODO).  Local constancy of
`t ↦ h⁰(L_t)` on `Spec A` is a *consequence* of this statement (the rank of
a free module over a nontrivial ring is well defined on connected
components), not a separate hypothesis.

This `Prop` is honestly TRUE for every finitely generated (equivalently,
noetherian quotient) `k`-algebra `A`; the gate `HasRigidPushforward`
quantifies it exactly there.  Truth for *arbitrary* `A` is not claimed —
that extension is milestone B2 (filtered colimits). -/
def RigidPushforwardLocallyFree (C : Over (Spec (CommRingCat.of k)))
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules,
    LineBundle.IsLocallyTrivial L →
    (∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t) →
    ∀ t : Spec (CommRingCat.of A),
      ∃ U : (Spec (CommRingCat.of A)).Opens, t ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj
            ((Scheme.Modules.pushforward
              (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L) ≅
          _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf)
            (ULift.{u} (Fin ((pullback.snd C.hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t))))

/-- **B3, step 1b (statement pin): the formation of the rigid pushforward
commutes with arbitrary base change** (Mumford AV II §5, Corollary 3;
campaign milestone B3(i), second conclusion).

Under the same hypotheses as `RigidPushforwardLocallyFree` (invertible `L`,
`h¹(L_t) = 0` at all scheme points), for **every** commutative ring
`A' : Type u` and **every** ring homomorphism `φ : A →+* A'` — no
finiteness, flatness or noetherian condition on `A'` (audit verdict in the
module docstring) — the canonical base-change comparison
`(Spec φ)^* (q_* L) ⟶ q'_* (g'^* L)` (`pushforwardBaseChangeMap`, the
adjunction mate) of the defining pullback square

```
  C_A ×_{Spec A} Spec A' --g'--> C_A
        |q'                        |q
        v                          v
     Spec A' ------Spec φ-----> Spec A
```

is an isomorphism.  The square is the *tautological* pullback of `q` along
`Spec φ`, so the statement needs no transport; the identification of its
corner with `C ×_k Spec A'` is the (separately proved, consumer-side)
pasting isomorphism. -/
def RigidPushforwardBaseChange (C : Over (Spec (CommRingCat.of k)))
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules,
    LineBundle.IsLocallyTrivial L →
    (∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t) →
    ∀ (A' : Type u) [CommRing A'] (φ : A →+* A'),
      IsIso (pushforwardBaseChangeMap
        (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        (Spec.map (CommRingCat.ofHom φ))
        (pullback.snd (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
          (Spec.map (CommRingCat.ofHom φ)))
        (pullback.fst (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
          (Spec.map (CommRingCat.ofHom φ)))
        pullback.condition L)

/-- **The B3 gate** (`HasPicScheme` pattern).  **This class now has a
producer.**  `Adelic.instHasRigidPushforwardOfCurve`
(`Picard/RigidPushforwardGammaBaseChange.lean`) is a global instance for
every `C` that is smooth of relative dimension one, proper and geometrically
integral over `k`, so the `[HasRigidPushforward C]` binders below synthesize
rather than being assumed; `Adelic.hasRigidPushforward_p1Over` exhibits a
curve satisfying those three hypotheses, so the instance is not vacuous.

Content: for the smooth proper geometrically integral curve `C/k` of the
campaign, both B3 statement pins hold over every finitely generated
`k`-algebra `A` (Hilbert basis: such `A` is noetherian — the honest scope of
the Mumford AV II §5 two-term-complex argument; milestone B2 extends
consumers to arbitrary affine bases by filtered colimits).

Route of the discharge (this is what was executed, not a plan): push along
the finite `C_A ⟶ ℙ¹_A` (`finiteMapToP1BaseChange` below) and run the
two-term finite free replacement on the explicit 2-chart Čech complex of
`ℙ¹_A` (`p1BaseChangeCoverSquare` below).  The `locallyFree` field comes out
of that engine directly; the `baseChange` field descends along the affine
target `Spec A'` to a `Γ`-level bijectivity
(`Picard/RigidPushforwardAffineDescent.lean`) which the same engine's Čech
purity supplies (`Picard/RigidPushforwardGammaBaseChange.lean`).  The
risk-register fallback (direct Čech on a 2-affine cover of `C_A`) was not
needed. -/
class HasRigidPushforward (C : Over (Spec (CommRingCat.of k))) : Prop where
  /-- Rank-`χ` local freeness over every finitely generated `k`-algebra. -/
  locallyFree : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
    RigidPushforwardLocallyFree C A
  /-- Arbitrary base change over every finitely generated `k`-algebra. -/
  baseChange : ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A],
    RigidPushforwardBaseChange C A

section Extraction

variable (C : Over (Spec (CommRingCat.of k)))
variable (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- **B3 headline, local-freeness half** (extraction from the gate): for an
invertible `L` on `C_A` with fibrewise `h¹ = 0` at all scheme points, the
pushforward `q_* L` is, near every `t : Spec A`, free of rank
`h⁰(C_t, L_t) = χ(L_t)`. -/
theorem pushforward_locallyFree_of_h1_vanishing [HasRigidPushforward C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L)
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t)
    (t : Spec (CommRingCat.of A)) :
    ∃ U : (Spec (CommRingCat.of A)).Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj
          ((Scheme.Modules.pushforward
            (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L) ≅
        _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf)
          (ULift.{u} (Fin ((pullback.snd C.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t)))) :=
  HasRigidPushforward.locallyFree A L hL h1 t

/-- **B3 headline, base-change half** (extraction from the gate): under the
same hypotheses, the formation of `q_* L` commutes with every ring map
`A → A'`. -/
theorem pushforward_baseChange_of_h1_vanishing [HasRigidPushforward C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L)
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t)
    (A' : Type u) [CommRing A'] (φ : A →+* A') :
    IsIso (pushforwardBaseChangeMap
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (Spec.map (CommRingCat.ofHom φ))
      (pullback.snd (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        (Spec.map (CommRingCat.ofHom φ)))
      (pullback.fst (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        (Spec.map (CommRingCat.ofHom φ)))
      pullback.condition L) :=
  HasRigidPushforward.baseChange A L hL h1 A' φ

end Extraction

/-! ## §4. The rank-one corollary (B3, step 2) -/

section RankOneCorollary

/-- **Rank-one local freeness gives local triviality** (scaffold brick for the
B3 rank-one corollary): if every point of `X` has an open neighbourhood on
which `M` pulls back to the free module of rank one, then `M` is an
invertible sheaf in the project sense (`LineBundle.IsLocallyTrivial`:
trivializations on an *affine* cover).  Proof: shrink each neighbourhood to
an affine one (`exists_isAffineOpen_mem_and_subset`), restrict the
trivialization along the inclusion (pullback pseudofunctor coherences +
`pullbackFreeIso`), and identify the rank-one free module with the unit
(`coproductUniqueIso`, as in `LineBundle.freeUnitIso`). -/
theorem LineBundle.isLocallyTrivial_of_pointwise_free_one {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))) :
    LineBundle.IsLocallyTrivial M := by
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := h x
  obtain ⟨W, hW_aff, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hxU
  have hle : W ≤ U := hWU
  refine ⟨W, hxW, hW_aff, ⟨?_⟩⟩
  have e₁ : M.restrict W.ι ≅ (Scheme.Modules.pullback W.ι).obj M :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M
  have e₂ : (Scheme.Modules.pullback W.ι).obj M ≅
      (Scheme.Modules.pullback (X.homOfLE hle ≫ U.ι)).obj M :=
    ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).symm).app M
  have e₃ : (Scheme.Modules.pullback (X.homOfLE hle ≫ U.ι)).obj M ≅
      (Scheme.Modules.pullback (X.homOfLE hle)).obj
        ((Scheme.Modules.pullback U.ι).obj M) :=
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) U.ι).app M).symm
  have e₄ : (Scheme.Modules.pullback (X.homOfLE hle)).obj
        ((Scheme.Modules.pullback U.ι).obj M) ≅
      (Scheme.Modules.pullback (X.homOfLE hle)).obj
        (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) :=
    (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e
  have e₅ : (Scheme.Modules.pullback (X.homOfLE hle)).obj
        (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) ≅
      _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)) :=
    Scheme.Modules.pullbackFreeIso (X.homOfLE hle) (ULift.{u} (Fin 1))
  have e₆ : _root_.SheafOfModules.free (R := W.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)) ≅
      _root_.SheafOfModules.unit W.toScheme.ringCatSheaf :=
    Limits.coproductUniqueIso (fun (_ : ULift.{u} (Fin 1)) ↦
      _root_.SheafOfModules.unit W.toScheme.ringCatSheaf)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆

variable (C : Over (Spec (CommRingCat.of k)))
variable (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- **B3, step 2: the rank-one corollary** (campaign milestone B3(i),
corollary; Kleiman §5): if moreover `h⁰(C_t, L_t) = 1` at every scheme point
`t : Spec A` (so `χ ≡ 1` given `h¹ ≡ 0`), the pushforward `q_* L` is an
invertible sheaf on `Spec A`.  Proved from the gate via
`LineBundle.isLocallyTrivial_of_pointwise_free_one`.

**J2-interface TODO** (deliberately not pinned here — see the module
docstring): the continuation `counit section fibrewise nonzero ⟹ regular on
the integral fibres ⟹ canonical DivFamily` belongs to milestone J2, where
the target `DivFamily` shape is fixed. -/
theorem pushforward_isLocallyTrivial_of_h1_vanishing [HasRigidPushforward C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
    (hL : LineBundle.IsLocallyTrivial L)
    (h1 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t)
    (h0 : ∀ t : Spec (CommRingCat.of A),
      (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t = 1) :
    LineBundle.IsLocallyTrivial
      ((Scheme.Modules.pushforward
        (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L) := by
  apply LineBundle.isLocallyTrivial_of_pointwise_free_one
  intro t
  obtain ⟨U, htU, ⟨e⟩⟩ := pushforward_locallyFree_of_h1_vanishing C A L hL h1 t
  rw [h0 t] at e
  exact ⟨U, htU, ⟨e⟩⟩

end RankOneCorollary

end Scheme

/-! ## §5. The ℙ¹ reduction skeleton (Mumford AV II §5 route)

The B3 discharge route: push `L` forward along the finite map
`π_A : C_A ⟶ ℙ¹_A` (base change of the gate `HasFiniteMapToP1`'s finite
`C ⟶ ℙ¹`, which is exportable via choice — `finiteMapToP1` below — since
`IsFinite` is `Prop`-valued), then run the two-term finite free replacement
on the explicit 2-chart Čech complex of `ℙ¹_A`
(`p1BaseChangeCoverSquare` + `AffineCoverMVSquare.moduleSectionRes`/
`moduleSectionDiff`).  This section builds the *proved* part of that route:

* the base-changed finite map and its finiteness
  (`isFinite_finiteMapToP1BaseChange`, by base-change stability of
  `IsFinite` along the cartesian square `C_A = C ×_{ℙ¹} ℙ¹_A`);
* the pushforward factorization `q_* ≅ p_* ∘ (π_A)_*`
  (`pushforwardFactorThroughP1Iso`, pseudofunctoriality);
* the standard 2-chart affine cover of `ℙ¹_A`;
* the **reduction theorem** `rigidPushforwardLocallyFree_of_p1`:
  B3-local-freeness for `C_A` follows from the ℙ¹ engine
  (`P1RigidPushforwardStatement`) plus a named finite-pushforward transfer
  package (coherence, base-flatness, and fibrewise `h⁰`/`h¹` transfer along
  the affine map `π_A` — the honest dévissage lemmas of the B3 discharge,
  Stacks 01XZ/02KE-grade, taken as hypotheses here and proved in the B3
  session). -/

namespace Adelic

open Scheme

variable {k : Type u} [Field k]

/-- The projective line `ℙ¹_k` as an object of `Over (Spec k)` — the target
of the finite-map gate `HasFiniteMapToP1`. -/
noncomputable abbrev p1Over (k : Type u) [Field k] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))

/-- **Choice extraction of the finite map to `ℙ¹`** from the gate
`HasFiniteMapToP1` (audit note: the gate stores a `Prop`-valued existential,
so the morphism itself is exportable only via `Classical.choice`; all
downstream uses are propositional, so this is harmless).  Everything the
reduction needs about it is `isFinite_finiteMapToP1_left`. -/
noncomputable def finiteMapToP1 (C : Over (Spec (CommRingCat.of k))) [HasFiniteMapToP1 C] :
    C ⟶ p1Over k :=
  (HasFiniteMapToP1.nonempty_finite_map (C := C)).choose

instance isFinite_finiteMapToP1_left (C : Over (Spec (CommRingCat.of k)))
    [HasFiniteMapToP1 C] : IsFinite (finiteMapToP1 C).left :=
  (HasFiniteMapToP1.nonempty_finite_map (C := C)).choose_spec

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The chart projection `ℙ¹_A ⟶ ℙ¹_k` is affine: it is the base change of
the affine morphism `Spec A ⟶ Spec k`. -/
instance isAffineHom_p1BaseChange_fst :
    IsAffineHom (pullback.fst (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) (p1Over k).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k A))))

/-- **The standard 2-chart affine cover of `ℙ¹_A`**: the preimage of the
standard cover `p1CoverSquare` of `ℙ¹_k` under the (affine, being a base
change of the affine `Spec A ⟶ Spec k`) projection `ℙ¹_A ⟶ ℙ¹_k`.  The
two-term complex `moduleSectionRes`/`moduleSectionDiff` on this cover is
the explicit 2-chart Čech complex of `ℙ¹_A` that the Mumford AV II §5
finite free replacement consumes. -/
noncomputable def p1BaseChangeCoverSquare :
    (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).AffineCoverMVSquare :=
  @Scheme.AffineCoverMVSquare.preimage _ _ (p1CoverSquare k)
    (pullback.fst (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (isAffineHom_p1BaseChange_fst A)

variable (C : Over (Spec (CommRingCat.of k)))

/-- **The base-changed finite map `π_A : C_A ⟶ ℙ¹_A`**: the functorial map
between the pullbacks along `Spec A ⟶ Spec k` induced by the finite
`π : C ⟶ ℙ¹` of the gate. -/
noncomputable def finiteMapToP1BaseChange [HasFiniteMapToP1 C] :
    Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      Limits.pullback (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  pullback.map C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (finiteMapToP1 C).left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact (Over.w (finiteMapToP1 C)).symm)
    (by simp)

/-- `π_A` is a map of families over `Spec A`: it commutes with the two
projections (the triangle `q = π_A ≫ p`). -/
@[reassoc (attr := simp)]
lemma finiteMapToP1BaseChange_snd [HasFiniteMapToP1 C] :
    finiteMapToP1BaseChange A C ≫
        pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `π_A` covers `π` over the chart projections. -/
@[reassoc (attr := simp)]
lemma finiteMapToP1BaseChange_fst [HasFiniteMapToP1 C] :
    finiteMapToP1BaseChange A C ≫
        pullback.fst (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))) ≫
        (finiteMapToP1 C).left :=
  pullback.lift_fst _ _ _

/-- **The square `C_A → C, π_A ↓ π.left, ℙ¹_A → ℙ¹` is cartesian**:
`C_A = C ×_{ℙ¹} ℙ¹_A` (pasting of pullbacks over the common base
`Spec k`).  This exhibits `π_A` as the base change of the finite `π.left`
along `ℙ¹_A ⟶ ℙ¹`, whence its finiteness. -/
lemma isPullback_finiteMapToP1BaseChange [HasFiniteMapToP1 C] :
    IsPullback (pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (finiteMapToP1BaseChange A C)
      (finiteMapToP1 C).left
      (pullback.fst (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) := by
  have hs : IsPullback
      (pullback.fst C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      (finiteMapToP1BaseChange A C ≫
        pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
      ((finiteMapToP1 C).left ≫ (p1Over k).hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [finiteMapToP1BaseChange_snd, Over.w (finiteMapToP1 C)]
    exact IsPullback.of_hasPullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  exact IsPullback.of_bot hs (finiteMapToP1BaseChange_fst A C).symm
    (IsPullback.of_hasPullback (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))

/-- **`π_A` is finite** — `IsFinite` is stable under base change, and
`isPullback_finiteMapToP1BaseChange` exhibits `π_A` as a base change of the
finite `π.left`. -/
instance isFinite_finiteMapToP1BaseChange [HasFiniteMapToP1 C] :
    IsFinite (finiteMapToP1BaseChange A C) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
    (isPullback_finiteMapToP1BaseChange A C) inferInstance

/-- **The pushforward factorization `q_* L ≅ p_* ((π_A)_* L)`** along the
triangle `q = π_A ≫ p` (pseudofunctoriality of the module pushforward).
This is the formal half of the B3 reduction: local freeness of `q_* L` is
local freeness of `p_* M` for `M := (π_A)_* L` on `ℙ¹_A`. -/
noncomputable def pushforwardFactorThroughP1Iso [HasFiniteMapToP1 C]
    (L : (Limits.pullback C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules) :
    (Scheme.Modules.pushforward
        (pullback.snd C.hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj L ≅
      (Scheme.Modules.pushforward
        (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) :=
  (Scheme.Modules.pushforwardCongr (finiteMapToP1BaseChange_snd A C).symm).app L ≪≫
    ((Scheme.Modules.pushforwardComp (finiteMapToP1BaseChange A C)
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))).app L).symm

/-- **The ℙ¹ engine (statement pin)**: the Mumford AV II §5 conclusion for
the projective line — for every finitely presented `M` on `ℙ¹_A`, flat over
the base, with fibrewise `h¹ = 0` at all scheme points, the pushforward
`p_* M` is locally free of pointwise rank `h⁰(ℙ¹_t, M_t)`.  This is the
`ℙ¹` instance of B3's local-freeness half, at the generality (coherent flat
`M`, not just line bundles) the finite-pushforward reduction requires.
Honestly TRUE for noetherian `A` (the two-term finite free replacement on
the 2-chart Čech complex `p1BaseChangeCoverSquare`); consumed as an explicit
hypothesis by `rigidPushforwardLocallyFree_of_p1` and discharged in the B3
session. -/
def P1RigidPushforwardStatement (k : Type u) [Field k]
    (A : Type u) [CommRing A] [Algebra k A] : Prop :=
  ∀ M : (Limits.pullback (p1Over k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules,
    M.IsFinitePresentation →
    CoherentSheafFlat
      (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A)))) M →
    (∀ t : Spec (CommRingCat.of A),
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing M t) →
    ∀ t : Spec (CommRingCat.of A),
      ∃ U : (Spec (CommRingCat.of A)).Opens, t ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj
            ((Scheme.Modules.pushforward (pullback.snd (p1Over k).hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A))))).obj M) ≅
          _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf)
            (ULift.{u} (Fin ((pullback.snd (p1Over k).hom
              (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 M t))))

/-- **THE B3 REDUCTION** (campaign W1-B acceptance item): *B3 local freeness
for `C_A` follows from the ℙ¹ engine plus the finite-pushforward transfer
package along `π_A : C_A ⟶ ℙ¹_A`.*  Sorry-free; the four named hypotheses
are the honest dévissage lemmas of the B3 discharge session:

* `hfp` — the finite pushforward of an invertible module is finitely
  presented (finite morphisms are affine with module-finite section rings;
  Stacks 01XZ, 087T-grade);
* `hflat` — the finite pushforward stays flat over the base (affine
  pushforward does not change the underlying sections over affine bases);
* `hH1` — fibrewise Čech `h¹`-transfer: `H¹(ℙ¹_t, (π_A)_* L |_t) ≅
  H¹(C_t, L_t)` (exactness of affine pushforward + cohomology-and-base-change
  in the affine direction, Stacks 02KE/02KG-grade);
* `hH0` — the same transfer in degree 0 (`h⁰` match).

No finiteness on `A` is needed for this glue: the finiteness enters only
when discharging `hP1` (Mumford's argument needs `A` noetherian). -/
theorem rigidPushforwardLocallyFree_of_p1 [HasFiniteMapToP1 C]
    (hP1 : P1RigidPushforwardStatement k A)
    (hfp : ∀ L : (Limits.pullback C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules,
      LineBundle.IsLocallyTrivial L →
      ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L).IsFinitePresentation)
    (hflat : ∀ L : (Limits.pullback C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules,
      LineBundle.IsLocallyTrivial L →
      CoherentSheafFlat
        (pullback.snd (p1Over k).hom (Spec.map (CommRingCat.ofHom (algebraMap k A))))
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L))
    (hH1 : ∀ (L : (Limits.pullback C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
      (t : Spec (CommRingCat.of A)), LineBundle.IsLocallyTrivial L →
      (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing L t →
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).FiberH1Vanishing
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t)
    (hH0 : ∀ (L : (Limits.pullback C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Modules)
      (t : Spec (CommRingCat.of A)), LineBundle.IsLocallyTrivial L →
      (pullback.snd (p1Over k).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0
        ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L) t =
      (pullback.snd C.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).fiberH0 L t) :
    Scheme.RigidPushforwardLocallyFree C A := by
  intro L hL h1 t
  obtain ⟨U, htU, ⟨e⟩⟩ := hP1
    ((Scheme.Modules.pushforward (finiteMapToP1BaseChange A C)).obj L)
    (hfp L hL) (hflat L hL) (fun s => hH1 L s hL (h1 s)) t
  refine ⟨U, htU, ⟨?_⟩⟩
  rw [hH0 L t hL] at e
  exact (Scheme.Modules.pullback U.ι).mapIso (pushforwardFactorThroughP1Iso A C L) ≪≫ e

end Adelic

end AlgebraicGeometry
