/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowInvariantsLocalization

/-!
# `(A_b)^G = (A^G)_b`: the chart-overlap comparison, as an equality of subrings

`Albanese/SymPowInvariantsLocalization.lean` proves the *substantive half* of the
invariants-commute-with-localization comparison — an `awayMap`-fixed element of `A_b` has an
invariant numerator (`exists_invariant_numerator`) — and says, in its own scope section, what
it does **not** prove:

> The converse inclusion — a fraction with invariant numerator is `awayMap`-fixed — is *not*
> proved here. … So this file does **not** assert the equality `(A_b)^G = (A^G)_b` as a ring
> isomorphism.

This file closes that gap and states the comparison. What the gluing step of Milne III.3
Proposition 3.1 consumes on a chart overlap is: *an invariant section over the overlap is a
fraction with invariant numerator, and conversely*. That biconditional is
`mem_fixedAway_iff_exists_invariant_num` below.

One thing the sibling's own prediction got wrong, and it is why the converse is not one line:
it foresaw pushing the invariant numerator through `algebraMap`, which is indeed free
(`algebraMap_mem_fixedAway`), but cancelling the *denominator* needs `1/b` to be invariant too,
and that spends invariance of `b` a second time (`inv_mem_fixedAway`).

## What is proved

* `awayMap_mulSemiringAction` — the `awayMap`s of `Albanese/SymPowInvariantsLocalization.lean`
  assemble into a `MulSemiringAction G (Localization.Away b)`, so `FixedPoints.subring` applies
  to the localization and the statement `(A_b)^G` can even be *written*. Without this the
  comparison has no left-hand side.
* `mem_fixedPoints_away_of_invariant` — **the converse direction the sibling flagged**: the
  image of an invariant element is fixed, and so is `1/b` (as `b` is invariant), hence every
  fraction with invariant numerator and `b`-power denominator is fixed.
* `isUnit_algebraMap_fixedAway` — the image of `b` is a unit **of the invariants**, the witness
  produced from `IsLocalization.Away.algebraMap_isUnit` rather than taken as a hypothesis.
* `mem_fixedAway_iff_exists_invariant_num` — **the comparison**, both directions in one
  biconditional: an element of `A_b` is `G`-fixed iff it is a fraction with invariant numerator
  and `b`-power denominator. See §3 for why it is elementwise rather than an `IsLocalization`
  instance.

## Why no averaging, again

Nothing below divides by `|G|`. The sibling's clearing argument is characteristic-free, and
the converse direction is a computation with `awayMap_algebraMap`. `|G| = g!` may vanish in
`A` — the curve is over an arbitrary `k̄` — so an averaging route would exclude exactly the
characteristics the challenge is stated over.

## Scope — what this is not

This is one input to the gluing, not the gluing. It compares the *rings*, at a single
invariant `b`. Three things remain, and none is touched here:

* the geometric side — that `Spec ((A^G)_b)` is the basic open of `Spec (A^G)` cut out by `b`,
  and that it is the quotient of the corresponding basic open upstairs;
* the cocycle condition across three charts;
* `OrbitsInAffineOpen` for the curve's `C^n`, which is item 4 of
  `Albanese/StableAffineCoverGroup.lean`'s bill and the honest wall of this leg.

So `AlbaneseUP.lean`'s six `sorry`s are unchanged by this file, and the count in
`Albanese/StableAffineCoverGroup.lean` (3 supplied, 1 open) is unchanged: this sharpens an
input *inside* item 4's neighbourhood rather than discharging any item.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94. The classical statement is that
formation of invariants commutes with flat base change for a finite group; the special case of
a localization at an invariant element is the only one a Zariski gluing needs, and it is
elementary (SGA I V.1; Mumford, *Abelian Varieties* §7).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {G A : Type u} [Group G] [CommRing A] [MulSemiringAction G A]

/-! ## §1. The action on the localization

`awayMap` gives one ring endomorphism of `A_b` per `g : G`; to write `(A_b)^G` at all one needs
them bundled as a `MulSemiringAction`. Both laws are checked through
`IsLocalization.ringHom_ext` — two ring maps out of a localization agree as soon as they agree
on the image of `A` — where `awayMap_algebraMap` reduces each to the ring action on `A`. -/

/-- **`awayMap` is multiplicative in `g`.** Composing the transports of `g` and `h` is the
transport of `g * h`. Checked on the image of `A`, where all three are the ring action. -/
theorem awayMap_comp_awayMap (b : A) (hb : ∀ g : G, g • b = b) (g h : G) :
    (awayMap b hb g).comp (awayMap b hb h) = awayMap b hb (g * h) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers b) ?_
  ext a
  simp only [RingHom.comp_apply, awayMap_algebraMap b hb]
  rw [mul_smul]

/-- **`awayMap` at `1` is the identity.** -/
theorem awayMap_one (b : A) (hb : ∀ g : G, g • b = b) :
    awayMap b hb (1 : G) = RingHom.id (Localization.Away b) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers b) ?_
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply, awayMap_algebraMap b hb]
  rw [one_smul]

/-- **The `G`-action on the chart overlap, as a `MulSemiringAction`.**

Geometrically: `G` acts on the basic open of `Spec A` cut out by the invariant function `b`.
This is what lets `(A_b)^G` be written — `FixedPoints.subring` needs an action, not a family of
endomorphisms — so it is a prerequisite for the comparison of §3 rather than bookkeeping.

Marked `@[implicit_reducible]` because it is a `def` of class type: the linter requires it, and
the project's convention for a class-valued `def` that cannot be an `instance` is the same
(compare `Pic0.jacobianScheme_grpObj` in `Albanese/AlbaneseUP.lean`, deliberately not an
instance for a different reason — there, to stop `sorryAx` propagating by synthesis). -/
@[implicit_reducible]
noncomputable def awayMapMulSemiringAction (b : A) (hb : ∀ g : G, g • b = b) :
    MulSemiringAction G (Localization.Away b) where
  smul g x := awayMap b hb g x
  one_smul x := by
    change awayMap b hb (1 : G) x = x
    rw [awayMap_one b hb]; rfl
  mul_smul g h x := by
    change awayMap b hb (g * h) x = awayMap b hb g (awayMap b hb h x)
    rw [← awayMap_comp_awayMap b hb g h]; rfl
  smul_zero g := map_zero (awayMap b hb g)
  smul_add g x y := map_add (awayMap b hb g) x y
  smul_one g := map_one (awayMap b hb g)
  smul_mul g x y := map_mul (awayMap b hb g) x y

/-- **`(A_b)^G`, the invariants of the chart overlap.** Bundled as a `Subring` rather than
obtained from an `instance`, because the action `awayMapMulSemiringAction` depends on the
*proof* `hb` that `b` is invariant and so cannot be a typeclass instance. Everything below
uses this name together with `mem_fixedAway`, which is the only interface needed. -/
noncomputable def fixedAway (b : A) (hb : ∀ g : G, g • b = b) :
    Subring (Localization.Away b) :=
  letI := awayMapMulSemiringAction b hb
  FixedPoints.subring (Localization.Away b) G

/-- Membership in `(A_b)^G` is being fixed by every `awayMap`. -/
theorem mem_fixedAway {b : A} {hb : ∀ g : G, g • b = b} {x : Localization.Away b} :
    x ∈ fixedAway b hb ↔ ∀ g : G, awayMap b hb g x = x :=
  Iff.rfl

/-! ## §2. The converse direction: invariant numerators give fixed fractions

The sibling file proves that a fixed element *has* an invariant numerator, and flags the
converse as unproved. It is proved here, in the two pieces the comparison uses: the image of an
invariant element is fixed (`algebraMap_mem_fixedAway`), and the inverse of `b` is fixed
(`inv_mem_fixedAway`) — the second is where invariance of `b` is spent a second time. -/

/-- **The image of an invariant element is fixed.** This is the converse inclusion at the level
of numerators: `awayMap` acts on numerators, so an invariant numerator gives a fixed fraction
with denominator `1`. -/
theorem algebraMap_mem_fixedAway (b : A) (hb : ∀ g : G, g • b = b) {a : A}
    (ha : ∀ g : G, g • a = a) :
    algebraMap A (Localization.Away b) a ∈ fixedAway b hb := by
  refine mem_fixedAway.mpr fun g => ?_
  rw [awayMap_algebraMap b hb, ha g]

/-- **An inverse of an invariant element is itself invariant.** Stated for a two-sided inverse
`y` of the image of `b`, so no unit hypothesis has to be *supplied*: the witness comes from
`IsLocalization.Away.algebraMap_isUnit` at the call sites below.

The argument: applying the ring map `awayMap g` to `b * y = 1` and using that `b` is fixed
exhibits `awayMap g y` as an inverse of `b`, and inverses in a commutative monoid are unique.

This is the second place invariance of `b` is spent — once in the sibling's clearing argument,
once here — and it is what makes the *denominators* of the comparison invariant as well as the
numerators. Note the sibling's scope section predicted only the numerator half. -/
theorem inv_mem_fixedAway (b : A) (hb : ∀ g : G, g • b = b)
    (y : Localization.Away b)
    (hy : algebraMap A (Localization.Away b) b * y = 1) :
    y ∈ fixedAway b hb := by
  refine mem_fixedAway.mpr fun g => ?_
  have hbg : awayMap b hb g (algebraMap A (Localization.Away b) b)
      = algebraMap A (Localization.Away b) b := by
    rw [awayMap_algebraMap b hb, hb g]
  have hmul : algebraMap A (Localization.Away b) b * awayMap b hb g y = 1 := by
    rw [← hbg, ← map_mul, hy, map_one]
  calc awayMap b hb g y
      = (y * algebraMap A (Localization.Away b) b) * awayMap b hb g y := by
        rw [mul_comm y, hy, one_mul]
    _ = y * (algebraMap A (Localization.Away b) b * awayMap b hb g y) := by rw [mul_assoc]
    _ = y := by rw [hmul, mul_one]

/-! ## §3. The comparison

The two halves combine into: an element of `A_b` is `G`-fixed **iff** it is a fraction with
invariant numerator and `b`-power denominator. That is the content of `(A_b)^G = (A^G)_b` in the
form a Zariski gluing consumes — the invariants of a chart overlap are determined by the
invariants of the chart, no new sections appearing after localizing.

**Stated elementwise, deliberately, and this is a scope limit not a style choice.** It would be
more quotable as `IsLocalization.Away (image of b) ((A_b)^G)` over the ring `A^G`. That spelling
needs an `Algebra (A^G) ((A_b)^G)` instance, and the action `awayMapMulSemiringAction` depends on
the *proof* `hb`, so no such instance can be synthesized; supplying it by hand is bookkeeping
that would sit between the two facts below and any consumer. The elementwise form is what the
overlap comparison actually applies, so it is what is proved. Anyone wanting the
`IsLocalization` spelling has the three clauses here (`isUnit_algebraMap_fixedAway`, the forward
and backward directions) and needs only to thread the algebra structure. -/

/-- **The image of `b` is a unit *of the invariants*, not merely of `A_b`.**

`IsLocalization.Away.algebraMap_isUnit` gives invertibility in `A_b` with no hypothesis; the
content here is that the inverse lies in `(A_b)^G`, which is `inv_mem_fixedAway`. So the unit is
produced, not assumed — the statement takes no witness as an argument.

Geometrically it is the statement that `D(b)` upstairs is the preimage of `D(b)` on the
quotient; it is also the `map_units` clause anyone threading the `IsLocalization` spelling
would need (see §3). -/
theorem isUnit_algebraMap_fixedAway (b : A) (hb : ∀ g : G, g • b = b) :
    IsUnit (⟨algebraMap A (Localization.Away b) b,
      algebraMap_mem_fixedAway b hb hb⟩ : fixedAway b hb) := by
  obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b
  have hy : algebraMap A (Localization.Away b) b
      * ((v⁻¹ : (Localization.Away b)ˣ) : Localization.Away b) = 1 := by
    rw [← hv]; exact v.mul_inv
  have hy' : ((v⁻¹ : (Localization.Away b)ˣ) : Localization.Away b)
      * algebraMap A (Localization.Away b) b = 1 := by
    rw [mul_comm]; exact hy
  refine isUnit_iff_exists.mpr ⟨⟨_, inv_mem_fixedAway b hb _ hy⟩, ?_, ?_⟩
  · exact Subtype.ext hy
  · exact Subtype.ext hy'

/-- **The comparison, in the form the gluing consumes: `(A_b)^G` is `(A^G)` with `b` inverted.**

Precisely: every element of `(A_b)^G` is `a / b^n` for an *invariant* `a`, and two invariants
with the same image differ by `b`-torsion. Stated elementwise rather than as an
`IsLocalization` instance because the `A^G`-algebra structure on `(A_b)^G` is not available by
synthesis (the action depends on the proof `hb`), and threading it would obscure that the two
clauses are exactly the sibling's theorem plus §2.

The `n`-th power of `b` on the left is applied *inside* `A_b`; the point of the statement is
that the numerator `a` may be taken invariant, i.e. it comes from `A^G`. -/
theorem exists_invariant_num_den [Finite G] (b : A) (hb : ∀ g : G, g • b = b)
    (x : Localization.Away b) (hx : x ∈ fixedAway b hb) :
    ∃ (a : A) (n : ℕ), (∀ g : G, g • a = a) ∧
      x * algebraMap A (Localization.Away b) (b ^ n)
        = algebraMap A (Localization.Away b) a :=
  exists_invariant_numerator b hb x (mem_fixedAway.mp hx)

/-- **Both directions in one statement**: for an element of `A_b`, being `G`-fixed is equivalent
to admitting a representation as a fraction with invariant numerator and `b`-power denominator.

Forward is the sibling's clearing argument (`exists_invariant_numerator`); backward is the
computation that `awayMap g` fixes the equation defining the fraction, using that both `a` and
`b` are invariant, plus cancellation of the unit `b^n`. The unit is *obtained* from
`IsLocalization.Away.algebraMap_isUnit`, not taken as a hypothesis — a statement that took the
witness as an argument would only relocate the obligation.

Where the two hypotheses go: `[Finite G]` is spent only in the forward direction (the sibling
takes a maximum over `G` of finitely many exponents), and invariance of `b` is spent in both.

This is the statement that makes two chart quotients comparable: it says the invariants of the
overlap are *determined* by the invariants upstairs, with no new sections appearing after
localizing. -/
theorem mem_fixedAway_iff_exists_invariant_num [Finite G] (b : A) (hb : ∀ g : G, g • b = b)
    (x : Localization.Away b) :
    x ∈ fixedAway b hb ↔
      ∃ (a : A) (n : ℕ), (∀ g : G, g • a = a) ∧
        x * algebraMap A (Localization.Away b) (b ^ n)
          = algebraMap A (Localization.Away b) a := by
  refine ⟨exists_invariant_num_den b hb x, ?_⟩
  rintro ⟨a, n, ha, hxa⟩
  refine mem_fixedAway.mpr fun g => ?_
  -- `b ^ n` is a unit of `A_b`, so `x` is determined by `x * b ^ n`.
  have hunit : IsUnit (algebraMap A (Localization.Away b) (b ^ n)) := by
    rw [map_pow]
    exact IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away b) b n
  refine hunit.mul_left_inj.mp ?_
  -- Apply `awayMap g` to the defining equation; both `a` and `b` are invariant.
  have hg := congrArg (awayMap b hb g) hxa
  rw [map_mul, awayMap_algebraMap b hb, awayMap_algebraMap b hb, smul_pow', hb g, ha g] at hg
  rw [hg, hxa]

end AlgebraicGeometry
