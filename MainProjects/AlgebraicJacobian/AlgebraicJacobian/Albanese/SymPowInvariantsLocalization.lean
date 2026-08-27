/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowInvariants

/-!
# Invariants commute with localization at an invariant element

`Albanese/SymPowInvariants.lean` names the affine symmetric-power carrier: the quotient of
`Spec A` by a group action is `Spec (A^G)`. The next step of Milne III.3 Proposition 3.1 —
the gluing — needs to compare that quotient on two overlapping charts, and the overlaps of
an affine cover are localizations. So the comparison one needs is

`(A_b)^G = (A^G)_b`  for `b` an invariant element,

which mathlib does **not** have at this pin (measured: no lemma anywhere combines
`FixedPoints` / `Algebra.IsInvariant` with `Localization` in a commuting statement). This
file proves the substantive direction.

## Why there is no averaging argument here

Over a field of characteristic zero one divides by `|G|` and averages. That is unavailable:
the curve is over an arbitrary `k̄`, so `|G| = g!` may well be zero in `A`. The proof below
is characteristic-free and is the standard clearing argument:

an invariant `x ∈ A_b` is *some* fraction `a / b^n`; invariance says `g • a` and `a` have the
same image in `A_b` for each `g`, so some power of `b` kills their difference. `G` is finite,
so one power `b^m` works for all `g` at once. Then `b^m · a` is **honestly invariant** in `A`
— using that `b` itself is invariant — and `x = (b^m a) / b^{m+n}` exhibits `x` as a fraction
with invariant numerator.

Note where each hypothesis is spent: finiteness of `G` only takes a maximum over `G` of
finitely many exponents, and invariance of `b` is what makes `b^m · a` invariant rather than
merely `b^m`-torsion-equivalent to something invariant. Neither is decorative.

## Main results

* `powers_le_comap` — an invariant `b` has `g`-stable powers, the side condition
  `IsLocalization.map` consumes.
* `awayMap` — the induced action of `g` on `A_b`, with `awayMap_algebraMap` saying it is the
  action of `g` on numerators. This is the `G`-action on a chart overlap.
* `exists_invariant_numerator` — **the theorem**: an element of `A_b` fixed by every
  `awayMap` is a fraction whose numerator can be chosen invariant. This is the substantive
  half of `(A_b)^G = (A^G)_b`.

## What is deliberately not claimed

The converse inclusion — a fraction with invariant numerator is `awayMap`-fixed — is *not*
proved **in this file**. It is proved in `Albanese/SymPowInvariantsAwayEquiv.lean`
(`mem_fixedAway_iff_exists_invariant_num`, both directions), which also supplies the
`MulSemiringAction` on `A_b` that the phrase `(A_b)^G` needs in order to be *writable* at all.
Two corrections to what this paragraph used to say, both found by writing it:

* it predicted the converse would need "no finiteness" — correct — but also that it was a
  one-line push through `algebraMap`. That is only the numerator half. Cancelling the
  denominator needs `b` invertible in `A_b` *inside the invariants*, i.e. that `1/b` is itself
  fixed, which spends invariance of `b` a second time;
* so this file alone still does **not** assert `(A_b)^G = (A^G)_b`; it asserts the direction a
  gluing argument consumes — getting an invariant representative — which is the substantive
  one. Cite the sibling, not this file, for the equality.

Nor is this the gluing. It is one input to it: the comparison map on a single overlap. The
cocycle condition across three charts is untouched.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94. Consumer: the gluing step
scoped in `Albanese/SymPowColimit.lean` §6.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {G A : Type u} [Group G] [CommRing A] [MulSemiringAction G A]

/-! ## §1. The action transports to a localization at an invariant element -/

/-- **An invariant element has `g`-stable powers.** The side condition
`IsLocalization.map` needs in order to push `g` through the localization at `b`. -/
theorem powers_le_comap (b : A) (hb : ∀ g : G, g • b = b) (g : G) :
    Submonoid.powers b ≤
      Submonoid.comap (MulSemiringAction.toRingHom G A g) (Submonoid.powers b) := by
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  refine ⟨n, ?_⟩
  change b ^ n = g • (b ^ n)
  rw [smul_pow', hb g]

/-- **The induced action on the chart overlap `A_b`.** For `b` invariant, `g` acts on the
localization `A_b` by acting on numerators. Geometrically this is the action of `G` on a
basic open subset of `Spec A` cut out by an invariant function — i.e. on the overlap of two
charts of a `G`-stable affine cover. -/
noncomputable def awayMap (b : A) (hb : ∀ g : G, g • b = b) (g : G) :
    Localization.Away b →+* Localization.Away b :=
  IsLocalization.map (M := Submonoid.powers b) (T := Submonoid.powers b)
    (Localization.Away b) (MulSemiringAction.toRingHom G A g) (powers_le_comap b hb g)

/-- `awayMap` acts on numerators: it is the localization of the action. -/
@[simp]
theorem awayMap_algebraMap (b : A) (hb : ∀ g : G, g • b = b) (g : G) (a : A) :
    awayMap b hb g (algebraMap A (Localization.Away b) a)
      = algebraMap A (Localization.Away b) (g • a) :=
  IsLocalization.map_eq (powers_le_comap b hb g) a

/-! ## §2. Clearing denominators to reach an invariant numerator

The two steps of the characteristic-free argument, separated so each is checkable on its
own: first that a single `g` can be cleared, then that finitely many can be cleared
*simultaneously*. -/

/-- **One `g` can be cleared.** If `g • a` and `a` agree in `A_b` then some power of `b`
equalises them already in `A`. This is `IsLocalization.exists_of_eq` with the annihilator
recognised as a power of `b`. -/
theorem exists_pow_smul_eq (b a : A) (g : G)
    (h : algebraMap A (Localization.Away b) (g • a)
      = algebraMap A (Localization.Away b) a) :
    ∃ m : ℕ, b ^ m * (g • a) = b ^ m * a := by
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) h
  obtain ⟨m, hm⟩ := c.2
  refine ⟨m, ?_⟩
  have hbc : (b ^ m : A) = (c : A) := hm
  rw [hbc]
  exact hc

/-- **All of `G` can be cleared at once.** Finiteness of `G` enters here and only here:
take the supremum of the finitely many exponents. -/
theorem exists_uniform_pow_smul_eq [Finite G] (b a : A)
    (h : ∀ g : G, ∃ m : ℕ, b ^ m * (g • a) = b ^ m * a) :
    ∃ m : ℕ, ∀ g : G, b ^ m * (g • a) = b ^ m * a := by
  classical
  cases nonempty_fintype G
  choose m hm using h
  refine ⟨Finset.univ.sup m, fun g => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, Finset.univ.sup m = m g + k :=
    ⟨Finset.univ.sup m - m g, by
      have hle : m g ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ g)
      omega⟩
  rw [hk, pow_add]
  calc b ^ m g * b ^ k * (g • a)
      = b ^ k * (b ^ m g * (g • a)) := by ring
    _ = b ^ k * (b ^ m g * a) := by rw [hm g]
    _ = b ^ m g * b ^ k * a := by ring

/-- **`b^m · a` is invariant.** The step that uses invariance of `b`: once one power of `b`
equalises `g • a` and `a` for every `g`, the *element* `b^m · a` is fixed by `G`.

Without `hb` this would fail — `g • (b^m a) = (g • b)^m (g • a)`, and the first factor has
to come back. -/
theorem smul_pow_mul_eq (b a : A) (m : ℕ) (hb : ∀ g : G, g • b = b)
    (h : ∀ g : G, b ^ m * (g • a) = b ^ m * a) (g : G) :
    g • (b ^ m * a) = b ^ m * a := by
  rw [smul_mul', smul_pow', hb g, h g]

/-! ## §3. The theorem -/

/-- **The substantive half of `(A_b)^G = (A^G)_b`.**

An element `x` of the localization `A_b` fixed by the induced action of every `g` is a
fraction whose numerator may be chosen **invariant**: there are `a ∈ A` invariant and `n`
with `x · b^n = a` in `A_b`.

Characteristic-free — no averaging over `G`, which is unavailable since `|G|` may vanish in
`A`. The route is §2: pick any representative, clear each `g` (`exists_pow_smul_eq`), clear
all of them together (`exists_uniform_pow_smul_eq`, the only use of finiteness), then
`smul_pow_mul_eq` upgrades the cleared numerator to an honestly invariant element.

This is the comparison a gluing argument consumes on a chart overlap: an invariant section
over the overlap comes from an invariant section upstairs, after shrinking by a power of the
invariant function cutting the overlap out. -/
theorem exists_invariant_numerator [Finite G] (b : A) (hb : ∀ g : G, g • b = b)
    (x : Localization.Away b) (hx : ∀ g : G, awayMap b hb g x = x) :
    ∃ (a : A) (n : ℕ), (∀ g : G, g • a = a) ∧
      x * algebraMap A (Localization.Away b) (b ^ n)
        = algebraMap A (Localization.Away b) a := by
  classical
  obtain ⟨⟨a, d⟩, hxa⟩ := IsLocalization.surj (Submonoid.powers b) x
  obtain ⟨n, hn⟩ := d.2
  have hd : (d : A) = b ^ n := hn.symm
  -- Invariance of `x` moves to its numerator, as an equation in `A_b`.
  have key : ∀ g : G, algebraMap A (Localization.Away b) (g • a)
      = algebraMap A (Localization.Away b) a := by
    intro g
    have h1 := congrArg (awayMap b hb g) hxa
    rw [map_mul, hx g, awayMap_algebraMap, awayMap_algebraMap] at h1
    rw [hd, smul_pow', hb g, ← hd] at h1
    rw [← h1, hxa]
  -- Clear denominators uniformly, then read off the invariant numerator.
  obtain ⟨m, hm⟩ :=
    exists_uniform_pow_smul_eq b a (fun g => exists_pow_smul_eq b a g (key g))
  refine ⟨b ^ m * a, m + n, smul_pow_mul_eq b a m hb hm, ?_⟩
  -- Restate the defining equation of the representative with its denominator as `b ^ n`.
  have hx' : x * algebraMap A (Localization.Away b) (b ^ n)
      = algebraMap A (Localization.Away b) a := by rw [← hd]; exact hxa
  rw [pow_add, map_mul, map_mul]
  calc x * (algebraMap A (Localization.Away b) (b ^ m)
        * algebraMap A (Localization.Away b) (b ^ n))
      = (x * algebraMap A (Localization.Away b) (b ^ n))
          * algebraMap A (Localization.Away b) (b ^ m) := by ring
    _ = algebraMap A (Localization.Away b) a
          * algebraMap A (Localization.Away b) (b ^ m) := by rw [hx']
    _ = algebraMap A (Localization.Away b) (b ^ m)
          * algebraMap A (Localization.Away b) a := by ring

end AlgebraicGeometry
