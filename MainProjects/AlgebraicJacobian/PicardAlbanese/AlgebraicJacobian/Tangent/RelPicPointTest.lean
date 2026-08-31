/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.RelPic
import AlgebraicJacobian.Tangent.DualNumberTestObject

/-!
# The relative Picard group at a one-point test object (W5-T4, §6.0)

At a test object `T` whose underlying space is a **single point** — the dual numbers
`Spec k[ε]` and the monoidal unit `Spec k` are the two cases Wave 5 uses — the subgroup
`picFromBase C T` of classes pulled back from the base is **trivial**, so

```
relPic C T  ≃*  (C ⊗ T).left.CechPic
```

and the coset calculus of the relative Picard group disappears from the ε-kernel
computation entirely.

## Why this is cheap, and why it was not found earlier

`picFromBase C T` is the *range* of `CechPic.map (snd C T).left`, i.e. of a group
homomorphism **out of** `T.left.CechPic`. A one-point space admits no cover with a
nontrivial overlap, so its Čech `H¹` of units vanishes — this is
`Scheme.CechPic.subsingleton_of_subsingleton` (`Picard/Pic.lean`), landed with the Picard
group itself. The range of a homomorphism out of a subsingleton group is trivial, and that
is the whole proof.

The `informal/w5-t4-worksheet.md` risk register (R-T4-1) had listed this collapse as a
sub-cliff of brick T4-b, to be paid by proving that `Pic` of a finite product of Artin
local rings vanishes. That statement is true and is genuine commutative algebra; it is also
*not needed at a one-point test*, where the collapse is topological. The lesson recorded in
that worksheet's §6.0: search for the shape of the **object** (a one-point space), not for
the shape of the expected **argument** (Artin local rings). The general-coefficient form
does still need the algebra, and is out of scope here.

## Main declarations

* `AlgebraicGeometry.picFromBase_eq_bot_of_subsingleton` — the collapse.
* `AlgebraicGeometry.relPicMk_injective_of_subsingleton` — hence `relPicMk` is injective.
* `AlgebraicGeometry.relPicMulEquivCechPic` — the resulting isomorphism
  `relPic C T ≃* (C ⊗ T).left.CechPic`, with the computation rule
  `relPicMulEquivCechPic_relPicMk`.
* `AlgebraicGeometry.subsingleton_overDualNumber_left`,
  `AlgebraicGeometry.picFromBase_overDualNumber_eq_bot` — the two Wave-5 instances.
* `AlgebraicGeometry.relPicMulEquivCechPic_relPicMap` — the compatibility square: the
  equivalence intertwines `relPicMap` with `CechPic.map`. This is what makes the reduction
  usable rather than merely true, since Wave 5 computes the *kernel* of the `ε`-restriction,
  not just the groups at its two ends.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open AlgebraicGeometry.Scheme (CechPic)

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

/-! ## The collapse at a one-point test object -/

/-- **`picFromBase` is trivial at a one-point test object.** Classes on `C ⊗ T` pulled back
from `T` form the range of `CechPic.map (snd C T).left`; when `T.left` has a subsingleton
underlying space its Čech Picard group is trivial
(`Scheme.CechPic.subsingleton_of_subsingleton`), so that range is `⊥`.

No hypothesis on `C` whatsoever, and no commutative algebra: the argument is that a
one-point space has no cover with a nontrivial overlap. -/
theorem picFromBase_eq_bot_of_subsingleton (T : Over (Spec (.of k)))
    [Subsingleton T.left] : picFromBase C T = ⊥ := by
  refine le_antisymm (fun L hL => ?_) bot_le
  obtain ⟨N, hN⟩ := (mem_picFromBase_iff (C := C)).mp hL
  rw [← hN, Scheme.CechPic.eq_one_of_subsingleton _ N, map_one]
  exact Subgroup.mem_bot.mpr rfl

/-- **The projection to the relative Picard group is injective at a one-point test
object** — immediate from `picFromBase_eq_bot_of_subsingleton`, since a quotient by the
trivial subgroup separates points. Together with the landed `relPicMk_surjective` this makes
`relPicMk` bijective. -/
theorem relPicMk_injective_of_subsingleton (T : Over (Spec (.of k)))
    [Subsingleton T.left] : Function.Injective (relPicMk C T) := by
  intro x y hxy
  have h := (QuotientGroup.eq (s := picFromBase C T)).mp hxy
  rw [picFromBase_eq_bot_of_subsingleton C T, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h

/-- **`relPic C T ≃* Pic(C ⊗ T)` at a one-point test object.** The relative Picard group is
the *absolute* Čech Picard group of `C ⊗ T` there, because the subgroup being quotiented out
is trivial. This is what lets the Wave-5 ε-kernel computation be phrased on `CechPic`
directly, with no coset bookkeeping. -/
noncomputable def relPicMulEquivCechPic (T : Over (Spec (.of k))) [Subsingleton T.left] :
    relPic C T ≃* (C ⊗ T).left.CechPic :=
  (MulEquiv.ofBijective (relPicMk C T)
    ⟨relPicMk_injective_of_subsingleton C T, relPicMk_surjective C T⟩).symm

@[simp]
theorem relPicMulEquivCechPic_relPicMk (T : Over (Spec (.of k))) [Subsingleton T.left]
    (L : (C ⊗ T).left.CechPic) :
    relPicMulEquivCechPic C T (relPicMk C T L) = L :=
  (MulEquiv.ofBijective (relPicMk C T)
    ⟨relPicMk_injective_of_subsingleton C T, relPicMk_surjective C T⟩).symm_apply_apply L

/-! ## The two Wave-5 instances: `Spec k[ε]` and `Spec k` -/

/-- The dual-number test object has a one-point underlying space: `Spec` of a local ring
whose maximal ideal is nilpotent. -/
instance subsingleton_overDualNumber_left :
    Subsingleton (overDualNumber k).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (DualNumber k)))

/-- **`picFromBase` is trivial at the dual-number test** — the Wave-5 instance of
`picFromBase_eq_bot_of_subsingleton`, retiring the "picFromBase collapse" sub-cliff that
`informal/w5-t4-worksheet.md` §4 (R-T4-1) had priced as commutative algebra. -/
theorem picFromBase_overDualNumber_eq_bot :
    picFromBase C (overDualNumber k) = ⊥ :=
  picFromBase_eq_bot_of_subsingleton C _

/-- `relPic C (Spec k[ε]) ≃* Pic(C_ε)`: the ε-side of the Wave-5 kernel, with the relative
quotient removed. -/
noncomputable def relPicOverDualNumberMulEquivCechPic :
    relPic C (overDualNumber k) ≃* (C ⊗ overDualNumber k).left.CechPic :=
  relPicMulEquivCechPic C _

/-! ## The compatibility square (what makes the reduction usable, not merely true) -/

/-- **The equivalence intertwines restriction along `g` with pullback of Čech classes.**

Without this, `relPicMulEquivCechPic` would identify the two *groups* at each end of the
`ε`-restriction while saying nothing about the *map* between them — and it is the kernel of
that map that Wave 5 computes. With it, the statement
`ker(relPic(k[ε]) → relPic(k)) ≃ ker(CechPic(C_ε) → CechPic(C))` is immediate.

The proof is `relPicMap_mk`: the relative restriction is *defined* as `CechPic.map (C ◁ g)`
descended to the quotients, so once the quotient is trivial there is nothing left to check.
Recorded explicitly because "the groups agree" and "the maps agree" are different claims and
only the second one is usable. -/
theorem relPicMulEquivCechPic_relPicMap (T T' : Over (Spec (.of k)))
    [Subsingleton T.left] [Subsingleton T'.left] (g : T' ⟶ T) (x : relPic C T) :
    relPicMulEquivCechPic C T' (relPicMap C g x)
      = Scheme.CechPic.map (C ◁ g).left (relPicMulEquivCechPic C T x) := by
  induction x using relPic.ind with
  | mk L => rw [relPicMap_mk, relPicMulEquivCechPic_relPicMk, relPicMulEquivCechPic_relPicMk]

end AlgebraicGeometry
