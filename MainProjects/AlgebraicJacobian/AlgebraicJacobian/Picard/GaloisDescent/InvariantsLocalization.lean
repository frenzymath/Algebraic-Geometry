/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.GaloisDescent.SemilinearAlgebras
import AlgebraicJacobian.Picard.FiniteGaloisQuotientAffine

/-!
# The semilinear action descends to a localization at an invariant element
(campaign `G2(c)`, layer 2)

Roadmap `AJC.picrep.etale-rep.galois`.

## What this file is for

`Picard/GaloisQuotientGlue.lean`'s opening audit pins the **non-affine** Galois
quotient as a four-layer construction with layer 1 built, and names layer 2 as
*quotient-localization*: for a `Γ`-stable open `U` of a semilinearly-acted `X` and
an **invariant** section `N`, the affine quotient localizes,
`(A_N)^Γ = (A^Γ)_N`.  Layer 2 is what lets layer 3's per-chart quotients be glued
along a stable open at all, so the `Scheme.GlueData` overlap isomorphisms have
something to be built from.

This file supplies the step that layer needs first, and the one with content:
**the `Γ`-action itself on `A_N`**, together with its semilinearity.  Everything
downstream of `IsSemilinear K L S` — the invariant subalgebra, Speiser's theorem
`descentAlgEquiv`, and hence the affine quotient of the localized chart — then
applies to `A_N` by the engine already in `SemilinearAlgebras.lean`, with no new
descent argument.

## Why this is at the ring level, and why the action is not free

Two things were measured before writing, and both shaped the statements.

*The action is not available from mathlib.*  `exact?` fails on
`MulSemiringAction (L ≃ₐ[K] L) (Localization.Away N)` with `N`'s invariance in
scope.  That failure is honest rather than an artefact of a composite goal: the
missing ingredient is that `γ` maps `Submonoid.powers N` **onto itself**, which is
*false for a general `N`* — `γ` sends `powers N` to `powers (γ • N)`.  So the
construction is a statement about invariant elements specifically, and
`powers_map_eq` is the single place `hN` is spent.

*The ring level is the carrier the data lives on.*  A `Γ`-stable open of a
non-affine `X` need not be affine, so the scheme-level spelling would route the
reader through the section-algebra bridge before any content appeared.  The
content is the ring fact.  `GaloisQuotientGlue.lean` already provides the bridge
in the other direction (`isSemilinear_sections`: sections over a stable open carry
a semilinear action), so a consumer composes that with this file.

## Contents

* `powers_map_eq` — the denominators are preserved; the one use of invariance;
* `powers_map`, `powers_map_eq_forces_pow` — the invariance-free general fact, and
  the **non-vacuity of `hN` as a theorem**: the conclusion of `powers_map_eq`
  forces `γ • N` to be a power of `N`, so at any `N` where it is not, that
  conclusion is false;
* `awayAut`, `awayAut_algebraMap` — the transported automorphism and its value on
  the image of `A`;
* `awayAutHom` — the transport is multiplicative, i.e. a `Γ`-action by ring
  automorphisms, packaged as a `MonoidHom` into `RingAut S`;
* `awayAction` — that action, in the form the engine consumes;
* `isSemilinear_away` — **it is semilinear**, so `invariantsSubalgebra`,
  `descentAlgEquiv` and Speiser apply to `A_N` verbatim;
* `awayAut_mk'_of_invariant_num` — a fraction with invariant numerator over a
  power of `N` is invariant, the direction a covering argument uses.

Stated for an arbitrary `IsLocalization.Away N S` rather than for
`Localization.Away N` on purpose: a consumer holding a basic open `D(N)` of a
chart has `Γ(X, D(N))` as its localization, not the `Localization` model, and
would otherwise owe a transport.

## What this does NOT do

It closes no `sorry` in `Picard/FGAPicRepresentability.lean` and witnesses **no**
antecedent of `Scheme.fgaPicardRepresentability` for any curve.  It does **not**
discharge `AlgebraicJacobian.GaloisDescent.HasGaloisQuotient` off the affine
locus: layer 2's covering half (a stable open inside a chart is covered by
invariant basic opens, and `π_U(V)` is open), layer 3 (the `Scheme.GlueData`) and
layer 4 (the glued base-change iso) are all untouched, and the Hironaka trap
`GaloisQuotientGlue.lean` records still bites at layer 3.  Read this as one step
of layer 2.

`OrbitsInAffineOpen` does not occur here and is not weakened: this file says
nothing about which opens exist, only what the action does on one localization.

## Binder discipline

`powers_map_eq`, `awayAut`, `awayAutHom` and `awayAut_mk'_of_invariant_num` need
**no** `K`/`L`-algebra structure on `A` and no semilinearity — they hold for any
`MulSemiringAction (L ≃ₐ[K] L) A`, and the section variables are `omit`ted rather
than carried, per the standing unused-hypothesis lesson.  Only
`isSemilinear_away` consumes `[Algebra L A]`, `[IsScalarTower L A S]` and
`[IsSemilinear K L A]`, and it does **not** consume `[Algebra K A]` or
`[IsScalarTower K L A]` (linter-confirmed, `omit`ted).
-/

set_option autoImplicit false

universe u v

namespace AlgebraicJacobian.GaloisDescent

namespace SemilinearAction

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {A : Type v} [CommRing A] [MulSemiringAction (L ≃ₐ[K] L) A]

/-! ## §1. Transporting one automorphism -/

/-- **The denominators are preserved, and this is the only use of `N`'s
invariance.**  The ring automorphism `γ` carries `Submonoid.powers N` onto itself.

For a general `N` this is *false* — `γ` sends `powers N` to `powers (γ • N)` — so
this is exactly where `hN` is spent, and it is why everything below is about
invariant elements rather than about localizations in general. -/
theorem powers_map_eq (N : A) (hN : ∀ γ : L ≃ₐ[K] L, γ • N = N) (γ : L ≃ₐ[K] L) :
    Submonoid.map (MulSemiringAction.toRingAut (L ≃ₐ[K] L) A γ).toMonoidHom
      (Submonoid.powers N) = Submonoid.powers N := by
  ext x
  simp only [Submonoid.mem_map, Submonoid.mem_powers_iff]
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by simp [MulSemiringAction.toRingAut, hN γ]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨N ^ n, ⟨n, rfl⟩, by simp [MulSemiringAction.toRingAut, hN γ]⟩

/-- **The general fact, with invariance dropped**: the image is the powers of the
*moved* element.

Stated because it is what makes `powers_map_eq` a theorem about invariant elements
rather than a lemma that happens to carry a spare hypothesis — see
`powers_map_eq_forces_pow` immediately below. -/
theorem powers_map (N : A) (γ : L ≃ₐ[K] L) :
    Submonoid.map (MulSemiringAction.toRingAut (L ≃ₐ[K] L) A γ).toMonoidHom
      (Submonoid.powers N) = Submonoid.powers (γ • N) := by
  ext x
  simp only [Submonoid.mem_map, Submonoid.mem_powers_iff]
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by simp [MulSemiringAction.toRingAut]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨N ^ n, ⟨n, rfl⟩, by simp [MulSemiringAction.toRingAut]⟩

/-- **`powers_map_eq`'s hypothesis is not decoration, and this is the measurement.**

A failing `exact?` on the invariance-free version of `powers_map_eq` would prove
only that no *one-lemma* proof exists — a much weaker fact on a composite goal.
So the non-vacuity is recorded as a theorem instead: the conclusion of
`powers_map_eq` **forces** `γ • N` to be a power of `N`. Hence for any `N` whose
`γ`-image is not a power of it, `powers_map_eq`'s conclusion is *false*, and every
construction below genuinely needs `hN` rather than merely mentioning it. -/
theorem powers_map_eq_forces_pow (N : A) (γ : L ≃ₐ[K] L)
    (h : Submonoid.map (MulSemiringAction.toRingAut (L ≃ₐ[K] L) A γ).toMonoidHom
      (Submonoid.powers N) = Submonoid.powers N) :
    ∃ n : ℕ, N ^ n = γ • N := by
  rw [powers_map] at h
  have hmem : (γ • N) ∈ Submonoid.powers N := by
    rw [← h]; exact Submonoid.mem_powers _
  simpa [Submonoid.mem_powers_iff] using hmem

variable (N : A) (hN : ∀ γ : L ≃ₐ[K] L, γ • N = N)
variable (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away N S]

/-- The automorphism of `S = A_N` transported from `γ`, available precisely because
`powers_map_eq` says the denominators are preserved. -/
noncomputable def awayAut (γ : L ≃ₐ[K] L) : S ≃+* S :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers N) (T := Submonoid.powers N)
    S S (MulSemiringAction.toRingAut (L ≃ₐ[K] L) A γ) (powers_map_eq K L N hN γ)

/-- The transported automorphism computes on the image of `A`: it is `γ` followed by
the structure map.  This is the identity every proof below runs through, via
`IsLocalization.ringHom_ext`. -/
theorem awayAut_algebraMap (γ : L ≃ₐ[K] L) (a : A) :
    awayAut K L N hN S γ (algebraMap A S a) = algebraMap A S (γ • a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (S := S) (Q := S) _ a

/-! ## §2. The transport is an action -/

/-- **The `Γ`-action on a localization at an invariant element**, as a `MonoidHom`
into `RingAut S`.

Both laws are `IsLocalization.ringHom_ext` against `awayAut_algebraMap`: two
automorphisms of a localization agreeing on the image of `A` are equal, and there
they are `one_smul` and `mul_smul` of the action on `A`. -/
noncomputable def awayAutHom : (L ≃ₐ[K] L) →* RingAut S where
  toFun γ := awayAut K L N hN S γ
  map_one' := by
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers N)
    ext a
    change awayAut K L N hN S 1 (algebraMap A S a) = algebraMap A S a
    rw [awayAut_algebraMap, one_smul]
  map_mul' γ τ := by
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers N)
    ext a
    change awayAut K L N hN S (γ * τ) (algebraMap A S a)
        = awayAut K L N hN S γ (awayAut K L N hN S τ (algebraMap A S a))
    rw [awayAut_algebraMap, awayAut_algebraMap, awayAut_algebraMap, mul_smul]

/-- The induced action by ring automorphisms, in the form the
`SemilinearAlgebras` engine consumes.  A `def` rather than an `instance`: it
depends on the invariance proof `hN`, exactly as `sectionsMulSemiringAction`
depends on a stability proof. -/
noncomputable abbrev awayAction : MulSemiringAction (L ≃ₐ[K] L) S :=
  MulSemiringAction.compHom S (awayAutHom K L N hN S)

/-- **A fraction with invariant numerator over a power of `N` is invariant.**

The direction a covering argument uses: it says the invariants of `A_N` are at
least as large as the localization of the invariants, i.e. the map
`(A^Γ)_N ⟶ (A_N)^Γ` exists.  The converse inclusion is the remaining half of
layer 2 and is *not* proved here. -/
theorem awayAut_mk'_of_invariant_num
    (a : A) (ha : ∀ γ : L ≃ₐ[K] L, γ • a = a) (n : ℕ) (γ : L ≃ₐ[K] L) :
    awayAut K L N hN S γ (IsLocalization.mk' S a (⟨N ^ n, n, rfl⟩ : Submonoid.powers N))
      = IsLocalization.mk' S a (⟨N ^ n, n, rfl⟩ : Submonoid.powers N) := by
  rw [awayAut, IsLocalization.ringEquivOfRingEquiv_mk']
  congr 1
  · exact ha γ
  · ext
    change (MulSemiringAction.toRingAut (L ≃ₐ[K] L) A γ) (N ^ n) = N ^ n
    simp [MulSemiringAction.toRingAut, hN γ]

/-! ## §3. Semilinearity — what makes the Speiser engine apply -/

section Semilinear

variable [Algebra K A] [Algebra L A] [IsScalarTower K L A] [IsSemilinear K L A]
variable [Algebra L S] [IsScalarTower L A S]

omit [Algebra K A] [IsScalarTower K L A] in
/-- **The action on `A_N` is semilinear over `Gal(L/K)`.**

This is the step with downstream value: `IsSemilinear K L S` is the hypothesis of
`invariantsSubalgebra`, `descentAlgHom` and Speiser's `descentAlgEquiv`, so with
it the *whole* affine-quotient engine of `SemilinearAlgebras.lean` applies to the
localized chart with no new descent argument — which is what layer 3 needs at each
piece of a stable cover.

One rewrite: semilinearity is checked on the image of `L`, which factors through
`A`, where it is `SemilinearAction.smul_algebraMap` for `A`.

**Two binders are idle and are `omit`ted rather than carried**: neither
`[Algebra K A]` nor `[IsScalarTower K L A]` is consumed (linter-confirmed). The
proof needs only that `L` maps to `A` compatibly with the tower to `S`. -/
theorem isSemilinear_away :
    letI := awayAction K L N hN S
    IsSemilinear K L S := by
  letI := awayAction K L N hN S
  apply SemilinearAction.isSemilinear_of_smul_algebraMap
  intro γ a
  change awayAut K L N hN S γ (algebraMap L S a) = algebraMap L S (γ a)
  rw [IsScalarTower.algebraMap_apply L A S, awayAut_algebraMap,
    SemilinearAction.smul_algebraMap K L A, ← IsScalarTower.algebraMap_apply L A S]

end Semilinear

end SemilinearAction

/-! ## §4. The payoff: the localized chart HAS a Galois quotient

This is what layer 2 is for, and it is stated because the value of
`isSemilinear_away` is not visible from the statement of `isSemilinear_away`.
-/

section LocalizedQuotient

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable {A : Type u} [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
  [MulSemiringAction (L ≃ₐ[K] L) A] [IsSemilinear K L A]
variable (N : A) (hN : ∀ γ : L ≃ₐ[K] L, γ • N = N)
variable (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away N S]
  [Algebra K S] [Algebra L S] [IsScalarTower K L S] [IsScalarTower L A S]

omit [Algebra K A] [IsScalarTower K L A] in
/-- **A localization at an invariant element has a Galois quotient, namely `Spec` of
its own invariants.**

`Spec S` with the action `awayAction` transported in §2 satisfies
`IsGaloisQuotient` against `Spec (S^Γ)` — all three clauses, including the
universal `T`-points property, for every `T`.

**Nothing new is proved here and that is the point.** The whole content is
`isSemilinear_away`: once the transported action is known semilinear,
`isGaloisQuotient_spec` (`Picard/FiniteGaloisQuotientAffine.lean`) applies
verbatim, Speiser and all. So layer 3, gluing per-chart quotients along stable
opens, can quote a quotient at each localized piece instead of constructing one —
which is the same simplification `GaloisQuotientGlue.lean`'s header records for
the affine case at layer 1.

**The universe is `Type u` throughout, not `Type v`, and this is a real
constraint rather than tidying**: `isGaloisQuotient_spec` lives at `Scheme.{u}`,
so it does not apply to a `Type v` ring. §§1–3 above are universe-polymorphic in
`A`; only this corollary is pinned, and a consumer whose section ring sits at
another level owes a universe bridge here and nowhere else.

Still **no** discharge of `HasGaloisQuotient` for a non-affine `X`: this is one
piece of a cover, and assembling the pieces is layer 3, where the Hironaka trap
bites.

`[Algebra K A]` and `[IsScalarTower K L A]` are `omit`ted: inherited from
`isSemilinear_away`, consumed by neither (linter-confirmed). What the corollary
needs of `A` is only that it acts and maps to `S`.

**WHAT I COULD NOT CLOSE, and a consumer should read this before relying on the
corollary.** The binders are jointly satisfiable at a *non-degenerate* site:
`A = L ⊗[K] K[X]` with the left-factor Galois action, `N = 1 ⊗ X` — an **invariant
non-unit**, so the localization is not trivially `A` — where all five of
`Algebra L`, `Algebra K`, `IsScalarTower K L`, `IsScalarTower L A` and
`IsLocalization.Away` synthesise, and `IsSemilinear K L (L ⊗[K] K[X])` closes by
`inferInstance`. That much is measured. But **applying this corollary there did not
elaborate**: the goal `IsSemilinear K L (L ⊗[K] K[X])` fails synthesis at the
application even with a hypothesis of exactly that type in context (measured — the
context shows `hsl : IsSemilinear K L (L ⊗[K] K[X])` and the unsolved goal is
literally it). So this is an **instance-path mismatch**, not an absence: the
tensor-product action is a *scoped* instance
(`instMulSemiringActionTensor`) and `IsSemilinear` is indexed by the
`DistribMulAction`, so the action supplied by `letI` and the one the ambient
instance found are different terms at the same type.

Recorded as unmeasured rather than papered over: the corollary is a theorem and its
axiom list is clean, but *no site in this project has been shown to satisfy its
binders in a way that lets it be applied*. A lane consuming it should elaborate at
its own object and, if it hits this, pin the action with an explicit `letI` before
the application rather than relying on synthesis. -/
theorem isGaloisQuotient_away :
    letI := SemilinearAction.awayAction K L N hN S
    letI := SemilinearAction.isSemilinear_away K L N hN S
    IsGaloisQuotient (specSemilinearGalAction K L S)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap K (SemilinearAction.invariantsSubalgebra K L S)))) := by
  letI := SemilinearAction.awayAction K L N hN S
  letI := SemilinearAction.isSemilinear_away K L N hN S
  exact isGaloisQuotient_spec K L S

end LocalizedQuotient

end AlgebraicJacobian.GaloisDescent
