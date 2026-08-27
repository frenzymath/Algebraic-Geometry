/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Albanese.CodimOneExtension
import AlgebraicJacobian.Picard.SchemeKrullDimStalk
import AlgebraicJacobian.Picard.EmbeddingDimensionBound
import AlgebraicJacobian.Picard.Pic0AbelianVariety

/-!
# The dimension of `Pic⁰_{C/k}` is the genus

This file turns the tangent-space identity `dim_{κ(e)} m_e/m_e² = g(C)` at the
identity of `Pic⁰_{C/k}` (`Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne`,
`Picard/Pic0AbelianVariety.lean`) into a statement about the **dimension of the
scheme** `Pic⁰_{C/k}`, which is what Milne III.1 Rmk 1.4(e) — "the dimension of
`J` is the genus of `C`" — asserts and what
`Pic0Scheme.finrank_eq_genus` (`Picard/IdentityComponent.lean`) pins.

## Two inputs, and which of them was actually missing

The recorded blocker at `finrank_eq_genus` was the *dimension-theoretic* step,
priced as an absent mathlib API for `topologicalKrullDim`. That step is supplied
by `Picard/SchemeKrullDimStalk.lean`, from the definition of the invariant rather
than from a presentation. What remains here is the *local algebra*:

* **regularity of the stalk** at the point where the tangent space is computed
  — `Scheme.isRegularLocalRing_stalk_of_smooth_of_perfectField` below;
* the **≥ direction only** comes for free from data at the identity. The ≤
  direction genuinely needs information at every point, and is stated as a
  hypothesis (see `topologicalKrullDim_eq_genus_of_forall_ringKrullDim_stalk_le`).

## The generalisation this file contributes upstream of itself

`Albanese/CodimOneExtension.lean` already proves stalk regularity from
smoothness, as `isRegularLocalRing_stalk_of_smooth` — but over an
**algebraically closed** field, and with `[GeometricallyIrreducible]`,
`[IsSeparated]`, `[LocallyOfFiniteType]`, `[IsIntegral]`, `[IsReduced]` binders.
None of those is used by the argument: the chart step is mathlib's
`Smooth.exists_isStandardSmooth` (Stacks 00T7), which needs only smoothness, and
the algebra step is the project's own
`isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
(`Albanese/SmoothPrimeRegularity.lean`), which needs only `PerfectField`. So the
version proved here has `[Field k] [PerfectField k] [Smooth X.hom]` and nothing
else.

That matters for this lane specifically: `Pic⁰_{C/k}` lives over the *given* base
field `k`, not over `k̄`, and no descent step is available for regularity — so the
alg-closed version could not have been applied here at all. (`PerfectField` is
still an assumption on `k`, and a real one: it holds in characteristic zero and
for finite and algebraically closed fields, and fails for e.g. `𝔽_p(t)`.)
-/

universe u

open AlgebraicGeometry Order TopologicalSpace CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

/-- **Stalks of a smooth scheme over a perfect field are regular local rings**
(Stacks 00TT, Jacobian-criterion direction) — at **every** point, closed or not,
with no hypothesis on the scheme beyond smoothness of the structural morphism.

Two steps, both already in the tree:

* mathlib's `Smooth.exists_isStandardSmooth` (Stacks 00T7) gives an affine chart
  `V ∋ z` on which the section ring is standard-smooth over `Γ(Spec k, U)`, and
  `gammaSpecField_ringEquiv` identifies that base with `k`;
* the stalk is the localisation of `Γ(X, V)` at the prime of `z`
  (`IsAffineOpen.isLocalization_stalk`), and the project's Serre-free Stacks-00TT
  theorem at an arbitrary prime over a perfect field,
  `isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField`
  (`Albanese/SmoothPrimeRegularity.lean`), concludes.

**This is a strict generalisation of `isRegularLocalRing_stalk_of_smooth`**
(`Albanese/CodimOneExtension.lean`), which asks for `[IsAlgClosed kbar]` plus
`[GeometricallyIrreducible]`, `[IsSeparated]`, `[LocallyOfFiniteType]`,
`[IsIntegral]` and `[IsReduced]`. What is *measured* here is that the proof below
elaborates with all six absent simultaneously and `PerfectField` in place of
`IsAlgClosed` — which is the claim that matters, though it does not by itself
show each binder is individually unused in the original (that proof is a
different proof term). The alg-closedness enters the argument only through
`PerfectField`, which `IsAlgClosed` implies.

The generalisation is *load-bearing* for the Picard lane, not cosmetic: `Pic⁰_{C/k}`
sits over the given field `k`, and regularity of a stalk does not descend along
`Spec k̄ → Spec k` by any route in this tree, so the alg-closed form is unusable
here. -/
theorem isRegularLocalRing_stalk_of_smooth_of_perfectField
    {k : Type u} [Field k] [PerfectField k]
    (X : Over (Spec (.of k)))
    [Smooth X.hom]
    (z : X.left) :
    IsRegularLocalRing (X.left.presheaf.stalk z) := by
  obtain ⟨U, hU, V, hV, hzV, e, hSS⟩ :=
    AlgebraicGeometry.Smooth.exists_isStandardSmooth X.hom z
  -- Base identification `Γ(Spec k, U) ≃+* k`: `U` contains the image of `z`, so it
  -- is nonempty.
  let ε : k ≃+* Γ(Spec (.of k), U) :=
    (gammaSpecField_ringEquiv k U ⟨⟨_, e hzV⟩⟩).symm
  have hSS' : ((X.hom.appLE U V e).hom.comp ε.toRingHom).IsStandardSmooth :=
    RingHom.isStandardSmooth_respectsIso.2 _ ε hSS
  letI : Algebra k Γ(X.left, V) :=
    ((X.hom.appLE U V e).hom.comp ε.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmooth k Γ(X.left, V) := hSS'.toAlgebra
  letI : Algebra Γ(X.left, V) (X.left.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
  haveI hLoc : IsLocalization.AtPrime (X.left.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨z, hzV⟩
  have hp : (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.IsPrime := (hV.primeIdealOf ⟨z, hzV⟩).isPrime
  haveI : Nontrivial Γ(X.left, V) := by
    refine ⟨0, 1, fun h => hp.1 ?_⟩
    exact Ideal.eq_top_of_isUnit_mem _ (Submodule.zero_mem _) (h ▸ isUnit_one)
  letI : Algebra k (X.left.presheaf.stalk z) :=
    ((algebraMap Γ(X.left, V) (X.left.presheaf.stalk z)).comp
      (algebraMap k Γ(X.left, V))).toAlgebra
  haveI : IsScalarTower k Γ(X.left, V) (X.left.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact isRegularLocalRing_of_isLocalization_atPrime_of_isStandardSmooth_of_perfectField
    (k := k) (S := Γ(X.left, V)) _ hp (X.left.presheaf.stalk z)

namespace Pic0

/-- **`Pic⁰_{C/k}` is locally Noetherian** — free from finite type over a field,
via `Pic0.locallyOfFiniteType` and mathlib's
`LocallyOfFiniteType.isLocallyNoetherian`.

**NOT needed by anything in this file**, and worth saying so where a reader will
look. It was written to discharge an `[IsLocallyNoetherian X]` binder on
`Scheme.le_topologicalKrullDim_of_finrank_cotangentSpace`, and that binder was
dead: `class IsRegularLocalRing R extends IsLocalRing R, IsNoetherianRing R`, so
the regularity hypothesis sitting beside it already supplied the Noetherian
instance. The binder is gone and this helper no longer has a consumer here.

Kept rather than deleted because the statement is true, cheap, and the natural
thing for a *later* consumer to want — `IsLocallyNoetherian` is the hypothesis of
mathlib's Noetherian-scheme API, and the `≤` half of the dimension statement
(still open, see below) is likely to need it where no regularity hypothesis is in
scope. Do not read its presence as evidence that it is used. -/
theorem isLocallyNoetherian {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsLocallyNoetherian (Pic0Scheme C).left := by
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := Pic0.locallyOfFiniteType C
  exact LocallyOfFiniteType.isLocallyNoetherian (Pic0Scheme C).hom

/-- **The genus is a LOWER bound for the dimension of `Pic⁰_{C/k}`** — a
*reduction*, not an axiom-clean theorem: see the measurement note below.

**MEASURED (`#print axioms`, full-root import): this reports `sorryAx`.** It
consumes `Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne`, which is gated on
the open cocycle comparison
`Pic0.semilinearComparison_cotangentSpaceDual_h1Cok`
(`Picard/Pic0AbelianVariety.lean:805`, front (a) of this chapter). So the honest
reading is: the dimension inequality needs **nothing beyond** the tangent-space
identity plus regularity at one point — no new geometry, no quantifier over
points — but the tangent-space identity is itself not yet closed. Everything in
`Picard/SchemeKrullDimStalk.lean` that this rests on *is* axiom-clean; the leak is
inherited from front (a) alone.

This is the half of Milne III.1 Rmk 1.4(e) that the tangent-space computation
gives away for free, and it needs data at **one** point:

* `Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne` computes
  `dim_{κ(e)} m_e/m_e² = dim_k H¹(C, 𝒪_C) = g(C)` at the identity;
* at a regular point `IsRegularLocalRing.iff_finrank_cotangentSpace` turns that
  into `dim 𝒪_{Pic⁰, e} = g(C)`;
* and a stalk's dimension is at most the dimension of the scheme
  (`ringKrullDim_stalk_le_topologicalKrullDim`, from
  `Picard/SchemeKrullDimStalk.lean`).

Note what is *not* needed: no quantifier over the points of `Pic⁰`, no smoothness
of `Pic⁰` (only regularity at `e`), and no affine-local presentation — the
recorded route through `Algebra.IsStandardSmoothOfRelativeDimension` is not
taken. -/
theorem genus_le_topologicalKrullDim_of_isRegular {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hreg : IsRegularLocalRing ((Pic0Scheme C).left.presheaf.stalk
      ((identitySection C).base default))) :
    ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞)
      ≤ topologicalKrullDim (Pic0Scheme C).left :=
  le_topologicalKrullDim_of_finrank_cotangentSpace _ _ _ hreg
    (finrank_cotangentSpace_eq_finrank_hModuleOne C)

/-- **The genus lower bound, with regularity discharged from smoothness over a
perfect field.**

`Pic⁰_{C/k}` smooth over `k` (which is what `Pic0.smooth` asserts, and what
`Pic0.smooth_of_isReduced_algebraicClosureBaseChange` reduces to reducedness over
`k̄`) gives regularity of *every* stalk by
`Scheme.isRegularLocalRing_stalk_of_smooth_of_perfectField`, in particular at the
identity. So over a perfect base field the lower bound needs no regularity
hypothesis at all — only smoothness, which is front (b) of this chapter. -/
theorem genus_le_topologicalKrullDim_of_smooth {k : Type u} [Field k] [PerfectField k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hsm : Smooth (Pic0Scheme C).hom) :
    ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞)
      ≤ topologicalKrullDim (Pic0Scheme C).left := by
  haveI := hsm
  exact genus_le_topologicalKrullDim_of_isRegular C
    (Scheme.isRegularLocalRing_stalk_of_smooth_of_perfectField (Pic0Scheme C) _)

/-- **`dim Pic⁰_{C/k} = g(C)`** — Milne III.1 Rmk 1.4(e), from smoothness over a
perfect field plus a uniform upper bound on the local dimensions.

This is the honest factoring of `Pic0Scheme.finrank_eq_genus`
(`Picard/IdentityComponent.lean`), and it makes visible that the two directions
have genuinely different costs:

* **≥** is *reduced to front (a)* here — `genus_le_topologicalKrullDim_of_smooth`
  derives it from the tangent-space identity at the identity alone, adding no new
  obligation, but that identity is itself open, so this direction reports
  `sorryAx` (see the measurement note on
  `genus_le_topologicalKrullDim_of_isRegular`);
* **≤** is the hypothesis `hle`, and it cannot be obtained from data at one
  point: it says every local ring of `Pic⁰_{C/k}` has dimension at most `g`. On a
  smooth *equidimensional* scheme this is the statement that the relative
  dimension is `g`, i.e. exactly the content of
  `SmoothOfRelativeDimension (genus C) (Pic0Scheme C).hom`, which
  `Picard/IdentityComponent.lean` already flags as the cheaper target for
  consumers wanting a dimension index.

So the *dimension-theoretic* content is consumed, and what is left is one uniform
bound for `≤` plus front (a) for `≥`. This theorem reports `sorryAx` for the
latter reason; only the `Picard/SchemeKrullDimStalk.lean` bridge underneath is
axiom-clean.

⚠ **RETRACTED (run 0067 r6): the paragraph that stood here concluded "the `≤`
direction is genuinely absent rather than merely unlocated", and that was a
measurement of the wrong quantity.** What it correctly established is only that
`Albanese/StandardSmoothDimension.lean` has no `ringKrullDim` *upper* bound — its
`Algebra.IsStandardSmoothOfRelativeDimension.le_ringKrullDim_of_isLocalization_atPrime`
gives `n ≤ ringKrullDim Sₘ`, a lower bound at a maximal ideal, and every lemma in
that file points the same way because it exists to feed
`IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim`. That much stands.

What does not stand is the conclusion. This chapter's tangent leg produces
**cotangent** dimensions, not `ringKrullDim`, and

```
ringKrullDim R ≤ dim_{κ(R)} (m/m²)
```

holds for *every* Noetherian local ring — no regularity, no condition on the
residue field. `ringKrullDim_le_finrank_cotangentSpace`
(`Picard/EmbeddingDimensionBound.lean`) composes Krull's height theorem
(`ringKrullDim_le_spanFinrank_maximalIdeal`) with Nakayama
(`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`); both were
already in the pinned mathlib, and `spanFinrank` occurred in exactly one AJC file
for an unrelated purpose. Regularity is the case of *equality*
(`IsRegularLocalRing.iff_finrank_cotangentSpace`), which is the only form this
project had, and the `iff` is why the inequality was never noticed.

USE INSTEAD `topologicalKrullDim_le_genus_of_forall_finrank_cotangentSpace_le` and
`topologicalKrullDim_eq_genus_of_forall_finrank_cotangentSpace_le` below: the first
is **axiom-clean**, and both are free of `[PerfectField k]`, which this theorem
carries. What is genuinely still owed for `≤` is the uniform *cotangent* bound —
a statement about embedding dimensions rather than about dimension theory, and
`SmoothOfRelativeDimension (genus C) (Pic0Scheme C).hom` would supply it. -/
theorem topologicalKrullDim_eq_genus_of_forall_ringKrullDim_stalk_le
    {k : Type u} [Field k] [PerfectField k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hsm : Smooth (Pic0Scheme C).hom)
    (hle : ∀ z : (Pic0Scheme C).left,
      ringKrullDim ((Pic0Scheme C).left.presheaf.stalk z)
        ≤ ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (Pic0Scheme C).left
      = ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞) :=
  le_antisymm
    (Scheme.topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ hle)
    (genus_le_topologicalKrullDim_of_smooth C hsm)

/-! ### The `≤` bound restated in cotangent currency (run 0067 r6)

The `hle` hypothesis above asks for a bound on `ringKrullDim` at every point. The two
statements below ask instead for a bound on the **cotangent dimension** at every
point, which is the invariant the tangent-space leg of this chapter actually computes,
and they need neither regularity nor `PerfectField` to convert it. See
`Picard/EmbeddingDimensionBound.lean` for why the conversion is unconditional in this
direction only. -/

/-- **`dim Pic⁰_{C/k} ≤ g(C)` from a uniform bound on the cotangent spaces** — no
regularity, no `PerfectField`, no presentation.

This replaces the `ringKrullDim`-shaped hypothesis of
`topologicalKrullDim_eq_genus_of_forall_ringKrullDim_stalk_le` with a
cotangent-shaped one. The measurement recorded at that theorem — that the `≤`
direction is "genuinely absent rather than merely unlocated", having searched
`Albanese/StandardSmoothDimension.lean` for a `ringKrullDim` upper bound — was of the
wrong quantity: `ringKrullDim R ≤ dim_κ(m/m²)` holds for **every** Noetherian local
ring (`ringKrullDim_le_finrank_cotangentSpace`, Krull's height theorem composed with
Nakayama, both already in the pinned mathlib). What is genuinely still owed is the
uniform *cotangent* bound, and that is a statement about embedding dimensions rather
than about dimension theory.

`IsLocallyNoetherian (Pic0Scheme C).left` is supplied by `Pic0.isLocallyNoetherian`
above — the helper the previous session kept with the note "the ≤ half of the
dimension statement is likely to need it where no regularity hypothesis is in scope".
That is exactly this.

**AND THE `hle` HYPOTHESIS IS NO LONGER OPEN CONTENT (run 0067 r7).** The paragraph above
describes what is owed as "the uniform *cotangent* bound", a statement about embedding
dimensions. On a **group** scheme that is not a separate statement: translations are
automorphisms of the underlying scheme, so the embedding dimension is constant along a
translate orbit, and `Pic0.forall_finrank_cotangentSpace_le_of_homogeneous`
(`Picard/GroupSchemeHomogeneity.lean`) derives `hle` from the value at *one* point plus the
orbit condition. Since the value at the identity is an equality, one point serves both
directions of the dimension statement —
`Pic0.topologicalKrullDim_eq_genus_of_homogeneous` is the resulting form, axiom-clean.
Prefer that theorem to instantiating `hle` by hand.

**THE PRECEDING PARAGRAPH IS RETRACTED (run 0067 r8): `hle` IS STILL OPEN CONTENT, and the
"one point plus the orbit condition" route is not merely unfinished but VACUOUS for `g ≥ 1`.**
`Pic0.topologicalKrullDim_eq_zero_of_homogeneous`
(`Picard/HomogeneityOrbitCollapse.lean`) shows the orbit condition alone forces
`topologicalKrullDim Pic⁰ = 0`, hence `genus C = 0`. Reason: translations are isomorphisms of
schemes hence homeomorphisms, the identity point is closed, so "every point is a translate of
the identity" forces every point to be closed — `T1` — and a nonempty sober `T1` space has
dimension `0`. So do **not** prefer that theorem: instantiating `hle` by hand is the honest
route, and what it needs is a transport reaching **non-closed** points (a translation by a
point valued in an extension of `k`, or a density argument as in
`identityComponent_irreducibleSpace_of_isAlgClosed`). The general theorem below, which takes
`hle` as a hypothesis, is unaffected and remains correct. -/
theorem topologicalKrullDim_le_genus_of_forall_finrank_cotangentSpace_le
    {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hle : ∀ z : (Pic0Scheme C).left,
      Module.finrank (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk z))
          ≤ AlgebraicGeometry.genus C) :
    topologicalKrullDim (Pic0Scheme C).left
      ≤ ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞) := by
  haveI := isLocallyNoetherian C
  exact Scheme.topologicalKrullDim_le_of_forall_finrank_cotangentSpace_le
    (Pic0Scheme C).left _ hle

/-- **`dim Pic⁰_{C/k} = g(C)` with both halves in cotangent currency.**

The two directions and their genuinely different costs, now visible in one statement:

* `≤` consumes `hle`, a uniform bound on the embedding dimension at every point, and
  converts it with no side conditions at all;
* `≥` consumes regularity of the **single** stalk at the identity, which is
  irreducible — an embedding dimension bounds the Krull dimension from below only at a
  regular point (at a cusp it exceeds it) — together with the tangent-space identity
  `Pic0.finrank_cotangentSpace_eq_finrank_hModuleOne`, which supplies the value `g(C)`
  there and is front (a) of this chapter, still open.

Compare `topologicalKrullDim_eq_genus_of_forall_ringKrullDim_stalk_le`: that version
carries `[PerfectField k]`, because it discharges regularity from smoothness through
`Scheme.isRegularLocalRing_stalk_of_smooth_of_perfectField`, whose own upstream input
carries the binder irremovably. This version takes regularity at the identity as a
hypothesis instead and so is stated over an **arbitrary** field — which is what the
standing owner decision (inbox I-0491) requires of this leg. A caller over a perfect
field can still discharge `hreg` from smoothness by that route.

MEASURE BEFORE QUOTING: like everything downstream of front (a), this reports
`sorryAx` at the full root through the tangent-space identity. The dimension
machinery it rests on (`Picard/EmbeddingDimensionBound.lean`,
`Picard/SchemeKrullDimStalk.lean`) is axiom-clean. -/
theorem topologicalKrullDim_eq_genus_of_forall_finrank_cotangentSpace_le
    {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hle : ∀ z : (Pic0Scheme C).left,
      Module.finrank (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk z))
        (IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk z))
          ≤ AlgebraicGeometry.genus C)
    (hreg : IsRegularLocalRing ((Pic0Scheme C).left.presheaf.stalk
      ((identitySection C).base default))) :
    topologicalKrullDim (Pic0Scheme C).left
      = ((AlgebraicGeometry.genus C : ℕ) : WithBot ℕ∞) :=
  le_antisymm (topologicalKrullDim_le_genus_of_forall_finrank_cotangentSpace_le C hle)
    (genus_le_topologicalKrullDim_of_isRegular C hreg)

end Pic0

end AlgebraicGeometry.Scheme
