/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.DualNumberCarrier

/-!
# The `ε ↦ 0` reduction across the carrier translation (W5-T4 step (b-coeff))

`Tangent/DualNumberCarrier.lean` identifies the thickened sections with the dual numbers of the
original sections, naturally in the **open**. This file supplies the other direction — the one
the `ε`-kernel computation actually spends — namely that the section map induced by the `ε ↦ 0`
test-object morphism **is** `TrivSqZeroExt.fst`:

```
relSectionsMap C k[ε] k W ∘ dualNumberSections C  =  (· ⊗ₜ 1) ∘ TrivSqZeroExt.fst
```

(`AlgebraicGeometry.Over.relSectionsMap_dualNumberSections`), and on units the corresponding
statement with `TruncExpCech.unitsFst` (`Over.relSectionsMapUnits_dualNumberSectionsUnits`).

## Why this needs a `scoped` algebra instance, and where it comes from

The tree's coefficient-direction tool `AlgebraicGeometry.relSectionsMap`
(`Cohomology/RelativeSectionsLinear.lean`) binds `[Algebra R R'] [IsScalarTower k R R']`, and at
`R := k[ε]`, `R' := k` neither is found by instance search.

**Both exist upstream** — `TrivSqZeroExt.algebraBase` and the `IsScalarTower` immediately after it
(`Mathlib/Algebra/TrivSqZeroExt/Basic.lean:890, :897`) — but `algebraBase` is deliberately **not an
instance**, because (mathlib's own comment) it "creates a different
`Algebra (TrivSqZeroExt R' M) (TrivSqZeroExt R' M)` instance from `TrivSqZeroExt.algebra'`". So
`epsAlgebra`/`epsIsScalarTower` below are `scoped` **re-exposures**, not constructions: instances
only inside `namespace TruncExpCech.EpsilonReduction`, which a consumer opens explicitly, never in
ambient search. With them the whole landed `relSectionsMap` API applies unchanged —
`relSectionsMap_pullback`, `relSectionsMap_overAlgebraMap`, `relSectionsMap_resHom` — which is why
this file is short: the geometry was already proved, and so was the algebra.

**An earlier version of this docstring said mathlib "has none" and justified `scoped` by a diamond
with `Algebra k k`. Both were wrong** (reviewer finding, inbox `I-0634`; a clash between *different*
types is impossible, and the real clash is at `Algebra (tsze) (tsze)`). The pattern is `I-0567`'s —
*present upstream but deliberately not an instance*, like a `private` name — not absent
infrastructure.

The identification itself is then a `rfl`: with `epsAlgebra` in scope,
`algebraMap k[ε] k = TrivSqZeroExt.fst` **definitionally** (`algebraMap_eps_eq_fst`), so
`relSectionsMap_overAlgebraMap` computes the reduction directly and the `ε` component dies
because `algebraMap k[ε] k ε = 0`.

## Implementation notes

Two `rw` walls, both the elided-restriction-argument family recorded at
`Tangent/TwoChartNormalize.lean` and `informal/w5-t4-worksheet.md` §6.10(3), and both worked
around the same way — never fight them, close by `exact`:

* `map_add` of `relSectionsMap` will not `rw` into the goal, because the goal mentions
  `(C ⊗ overSpec k R).left` where the lemma mentions `relCurve C R` (equal by `rfl`, not
  syntactically). Apply it as a **term** via `RingHom.map_add` and `.trans`.
* the final `a + 0 = a` likewise resists `rw [add_zero]`; `exact add_zero _` closes it.

## Main declarations

* `TruncExpCech.EpsilonReduction.epsAlgebra` / `epsIsScalarTower` — the scoped instances.
* `TruncExpCech.EpsilonReduction.algebraMap_eps_eq_fst` — `algebraMap k[ε] k` is `fst` (`rfl`).
* `AlgebraicGeometry.Over.relSectionsMap_sectionsBaseChange_tmul` — the reduction on a pure
  tensor.
* `AlgebraicGeometry.Over.relSectionsMap_dualNumberSections` — **(b-coeff)**.
* `AlgebraicGeometry.Over.relSectionsMapUnits_dualNumberSectionsUnits` — the unit form, which
  is what the two-chart Čech comparison consumes.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §6.13.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open TensorProduct TruncExpCech DualNumber

namespace TruncExpCech

/-! ## The scoped algebra structure on the `ε ↦ 0` reduction -/

namespace EpsilonReduction

variable {k : Type u} [Field k]

/-- **`k[ε]` acts on `k` through `ε ↦ 0`** — a `scoped` instance wrapping **mathlib's own**
`TrivSqZeroExt.algebraBase`.

**Corrected 2026-07-28 (reviewer finding, inbox `I-0634`).** An earlier version of this file and of
`informal/w5-t4-worksheet.md` §6.14 said *"`relSectionsMap` needs an `Algebra k[ε] k`, and mathlib
has none"*. **That was false.** `Mathlib/Algebra/TrivSqZeroExt/Basic.lean:890` defines
`TrivSqZeroExt.algebraBase : Algebra (tsze R' M) R'` by exactly `fstHom`, and the next declaration
(`:897`) is the matching `IsScalarTower R' (tsze R' M) R'`. At `R' = M = k` those are precisely what
is needed, so this is a *rename*, not a construction.

**Why mathlib does not make it an instance** — quoting its own comment, not a guess: it "creates a
different `Algebra (TrivSqZeroExt R' M) (TrivSqZeroExt R' M)` instance from `TrivSqZeroExt.algebra'`".
So the clash is at `Algebra (tsze) (tsze)`, *not* the "diamond with `Algebra k k`" this file
previously claimed (a clash between different types is impossible). Keeping it `scoped` is right; the
reason recorded for it was wrong.

This is therefore the `I-0567` family — *present upstream but deliberately not an instance*, like a
`private` name — and **not** a case of absent infrastructure. -/
noncomputable scoped instance epsAlgebra : _root_.Algebra (DualNumber k) k :=
  TrivSqZeroExt.algebraBase k k

/-- `k → k[ε] → k` is the identity, so the two structure maps are compatible.

This is mathlib's `TrivSqZeroExt`-level instance (`Basic.lean:897`) at `R' = M = k`, re-exposed here
under `epsAlgebra`; it needs no proof of its own — see `epsAlgebra`'s docstring and `I-0634`. -/
scoped instance epsIsScalarTower : IsScalarTower k (DualNumber k) k :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := DualNumber k) (A := k) fun c => by
    change _ = TrivSqZeroExt.fst (algebraMap k (DualNumber k) c)
    simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- With `epsAlgebra` in scope, the structure map **is** `TrivSqZeroExt.fst`, definitionally.
This is what makes the reduction identification free rather than a computation. -/
theorem algebraMap_eps_eq_fst (x : DualNumber k) :
    algebraMap (DualNumber k) k x = TrivSqZeroExt.fst x :=
  rfl

/-- `ε` reduces to `0`. -/
@[simp]
theorem algebraMap_eps_eps : algebraMap (DualNumber k) k (ε : DualNumber k) = 0 :=
  rfl

end EpsilonReduction

end TruncExpCech

namespace AlgebraicGeometry

open TruncExpCech.EpsilonReduction

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))

attribute [local instance] Over.sectionsAlgebra

/-! ## The reduction on a pure tensor -/

/-- **The `ε ↦ 0` reduction on a pure tensor**: the relative sections comparison map along
`k[ε] → k` carries the base change of `s ⊗ a` to the base change of `s ⊗ fst a`.

Proved entirely from the landed `relSectionsMap` calculus: split the base change of a pure
tensor into the curve pullback times the structure pullback
(`Over.sectionsBaseChange_tmul` and `Over.sectionsBaseChange_one_tmul_overAlgebraMap`), then
apply `relSectionsMap_pullback` to the first factor and `relSectionsMap_overAlgebraMap` to the
second. No new geometry. -/
theorem Over.relSectionsMap_sectionsBaseChange_tmul {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (s : Γ(C.left, W)) (a : DualNumber k) :
    relSectionsMap C (DualNumber k) k W
        (Over.sectionsBaseChange C (DualNumber k) hW hW' (s ⊗ₜ a))
      = Over.sectionsBaseChange C k hW hW' (s ⊗ₜ algebraMap (DualNumber k) k a) := by
  have h1 : Over.sectionsBaseChange C (DualNumber k) hW hW' (s ⊗ₜ a)
      = relPullbackSection C (DualNumber k) W s
        * (relCurve C (DualNumber k)).overAlgebraMap (DualNumber k)
            ((fst C (overSpec k (DualNumber k))).left ⁻¹ᵁ W) a := by
    rw [Over.sectionsBaseChange_tmul]; rfl
  have h2 : Over.sectionsBaseChange C k hW hW' (s ⊗ₜ algebraMap (DualNumber k) k a)
      = relPullbackSection C k W s
        * (relCurve C k).overAlgebraMap k ((fst C (overSpec k k)).left ⁻¹ᵁ W)
            (algebraMap (DualNumber k) k a) := by
    rw [Over.sectionsBaseChange_tmul]; rfl
  rw [h1, h2, map_mul, relSectionsMap_pullback, relSectionsMap_overAlgebraMap]

/-! ## (b-coeff): the reduction is `fst` -/

/-- **(b-coeff): the `ε ↦ 0` section map is `TrivSqZeroExt.fst` across the carrier
translation.** Precisely: reducing a thickened section obtained from a dual number `x` yields
the base change of `fst x ⊗ 1`.

This is the statement the `ε`-kernel computation spends. Together with
`Over.resHom_dualNumberSections` (naturality in the open) it makes
`Tangent/DualNumberCarrier.lean`'s equivalence a translation of the *reduction*, not merely of
the two carriers at its ends — the distinction inbox `I-0571` is about, and the reason a
kernel computation cannot be built from the equivalence alone.

Proof: expand `x = fst x ⊗ 1 + snd x ⊗ ε` (`baseChangeAlgEquiv_symm_apply`), apply the pure
tensor lemma to both summands, and note the second dies because `fst ε = 0`. -/
theorem Over.relSectionsMap_dualNumberSections {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (x : DualNumber Γ(C.left, W)) :
    relSectionsMap C (DualNumber k) k W (Over.dualNumberSections C hW hW' x)
      = Over.sectionsBaseChange C k hW hW' (TrivSqZeroExt.fst x ⊗ₜ (1 : k)) := by
  have hA := Over.relSectionsMap_sectionsBaseChange_tmul C hW hW' (TrivSqZeroExt.fst x)
    (1 : DualNumber k)
  have hB := Over.relSectionsMap_sectionsBaseChange_tmul C hW hW' (TrivSqZeroExt.snd x)
    (ε : DualNumber k)
  rw [algebraMap_eps_eps, TensorProduct.tmul_zero, map_zero] at hB
  rw [map_one] at hA
  rw [Over.dualNumberSections_apply, baseChangeAlgEquiv_symm_apply, map_add]
  refine ((relSectionsMap C (DualNumber k) k W).map_add _ _).trans ?_
  rw [hA, hB]
  exact add_zero _

/-! ## The unit form, which the Čech comparison consumes -/

/-- **(b-coeff) on units**: the reduction of the unit attached to `u : (Γ(C, W)[ε])ˣ` is the
unit attached to `unitsFst u = fst u`.

This is the form the two-chart Čech comparison consumes: the engine produces overlap *units*
(`truncExpUnit`) and `TwoChartNaturality.map_twoChartClassHom` consumes them, so the
intertwining has to be stated on `Units`. Obtained from
`Over.relSectionsMap_dualNumberSections` by `Units.ext`. -/
theorem Over.relSectionsMapUnits_dualNumberSectionsUnits {W : C.left.Opens}
    (hW : IsCompact (W : Set C.left)) (hW' : IsQuasiSeparated (W : Set C.left))
    (u : (DualNumber Γ(C.left, W))ˣ) :
    (Units.map (relSectionsMap C (DualNumber k) k W).toMonoidHom
        (Over.dualNumberSectionsUnits C hW hW' u) :
          Γ(relCurve C k, (fst C (overSpec k k)).left ⁻¹ᵁ W))
      = Over.sectionsBaseChange C k hW hW'
          ((unitsFst u : Γ(C.left, W)) ⊗ₜ (1 : k)) :=
  Over.relSectionsMap_dualNumberSections C hW hW' (u : DualNumber Γ(C.left, W))

end AlgebraicGeometry
