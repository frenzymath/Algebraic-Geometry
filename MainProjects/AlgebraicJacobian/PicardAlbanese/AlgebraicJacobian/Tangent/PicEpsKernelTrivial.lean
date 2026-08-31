/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Tangent.ReductionTrivialCyclic
import AlgebraicJacobian.Tangent.DualNumberFstKernel
import AlgebraicJacobian.Tangent.DualNumberChartPic

/-!
# A `Pic A[ε]` class trivial along `ε ↦ 0` is trivial (W5-T4, the algebraic half of (iii-c2-aff))

The landed module-level tower of clause (iii-c2-aff) —
`ReductionTrivialCyclic` → `CyclicQuotientGenerator` → `NilpotentThickeningFree` — concludes
`Module.Free A[ε] M` from freeness of the base change along the **ring quotient** `A[ε] ⧸ (ε)`.
What the geometry supplies is triviality of the base change along **`fst : A[ε] → A`**. This file
crosses between the two and lifts the result to the Picard group:

```
Pic.mapRingHom fstRingHom M = 1   ⟹   M = 1
```

## The crossing is one `rfl`, and three docstrings had described it without writing it

`Tangent/DualNumberFstKernel.lean` proved `A[ε] ⧸ (ε) ≃+* A` precisely so this could be said, and
its docstring named the consumer ("the form a consumer feeds to `QuotSMulTop.equivQuotTensor`")
without supplying the triangle. `ReductionTrivialCyclic`'s `free_of_free_baseChange_eps` recorded
the same gap from the other side ("the base change is taken along `A[ε] ⧸ (ε)`, not along `A` — the
two are isomorphic but the statement is phrased on the quotient so that no ring identification is
needed *here*"). The identification is `quotientSpanEpsRingEquiv_comp_mk` below: composing the
equivalence back with the quotient map returns `fstRingHom` **definitionally**, the kernel
computation having been spent inside the equivalence.

## Two spelling constraints, both measured and both load-bearing

**The factoring must be applied FORWARDS.** `rw [← quotientSpanEpsRingEquiv_comp_mk, …] at h`
exceeds the default heartbeats at `whnf`; `refine … ?_` and then rewriting the *goal* costs
nothing. Same lemmas, opposite direction — `I-0685`'s family one step on: not only *whether* two
spellings are `rfl`-equal, but *which side* you unfold.

**`Ideal.Quotient.algebraMap_eq` is applied right-to-left.** The middle lemma is stated with
`Ideal.Quotient.mk`, so `CommRing.Pic.mapRingHom_algebraMap` needs the goal converted to
`algebraMap` first, and the forward orientation of `algebraMap_eq` finds no pattern.

**`maxSynthPendingDepth = 3` (from `lakefile.toml`) is REQUIRED for both statements**, and this is
the sharp warning of the file. Without it, `CommRing.Pic.mapRingHom (Ideal.Quotient.mk …)` does not
elaborate at all: the quotient's structure arrives as `Ideal.Quotient.ring` and the argument is
rejected against `mapRingHom`'s `CommSemiring` face. So a hand-rolled `lean` invocation that omits
the project's `leanOptions` reports three errors here that a `lake` build and the LSP do not see.

> **A lock-free kernel check must carry the lakefile's `leanOptions`.** Measured this session: the
> option-starved invocation reported an "instance-keying" failure and I diagnosed it as a
> *conflict between import sets* — a plausible, precise, and entirely wrong conclusion. Re-run with
> `-D maxSynthPendingDepth=3` and every spelling elaborates, including the one the false diagnosis
> had ruled out. The check is still worth running (it caught a real namespace error in this same
> pass), but read a failure it reports against a `lake`-green file as a possible OPTION gap before
> reading it as mathematics.

**The cheap immunity, adopted from `ajcr-charts` (inbox `I-0494`): this file states
`set_option maxSynthPendingDepth 3` itself.** A file-local `set_option` travels with the module, so
any lock-free check gets the option whether or not the command line supplies it, and the
project-level `leanOptions` becomes a convenience rather than a correctness dependency. Worth doing
in any module whose elaboration needs a non-default option.

## Main declarations

* `TruncExpCech.quotientSpanEpsRingEquiv_comp_mk` — `fst` factors through `A[ε] ⧸ (ε)`, by `rfl`.
* `TruncExpCech.pic_mapRingHom_mk_eq_one_of_fst` — the same triviality along the ε-quotient.
* `TruncExpCech.pic_eq_one_of_mapRingHom_fst` — hence the class itself is trivial.

Reference: Kleiman, "The Picard scheme", §5 Thm. 5.11 (arXiv:math/0504020);
`informal/w5-t4-worksheet.md` §§6.17, 6.27.
-/

set_option autoImplicit false

-- Required for `Pic.mapRingHom` at `Ideal.Quotient.mk`; `lakefile.toml` sets it globally, but
-- stating it in the file makes the module immune to a lock-free check that forgets the project's
-- `leanOptions` (see the docstring above, and `ajcr-charts` on inbox `I-0494`).
set_option maxSynthPendingDepth 3

universe u

open TrivSqZeroExt DualNumber

namespace TruncExpCech

variable {A : Type u} [CommRing A]

/-- **`ε ↦ 0` factors through the quotient by `(ε)`, definitionally.**

`quotientSpanEpsRingEquiv : A[ε] ⧸ (ε) ≃+* A` (`Tangent/DualNumberFstKernel.lean`) is the first
isomorphism theorem for `fst` with `ker_fstRingHom` substituted, so composing it back with the
quotient map returns `fstRingHom` on the nose.

This is the link between the two ways the geometry and the algebra speak about `ε ↦ 0`: a base
change along `fst` on one side, a base change along a ring **quotient** — the only form
`QuotSMulTop.equivQuotTensor` accepts — on the other. -/
theorem quotientSpanEpsRingEquiv_comp_mk :
    (quotientSpanEpsRingEquiv (A := A) :
        (DualNumber A ⧸ Ideal.span {(ε : DualNumber A)}) →+* A).comp
        (Ideal.Quotient.mk (Ideal.span {(ε : DualNumber A)}))
      = (fstRingHom (R := A)) := rfl

/-- Triviality along `ε ↦ 0`, restated along the ε-quotient.

A separate declaration on purpose: it must be proved **forwards** (rewriting the goal), the
backwards form on the hypothesis exceeding the default heartbeat budget at `whnf`. -/
theorem pic_mapRingHom_mk_eq_one_of_fst (M : CommRing.Pic (DualNumber A))
    (h : CommRing.Pic.mapRingHom (fstRingHom (R := A)) M = 1) :
    CommRing.Pic.mapRingHom (Ideal.Quotient.mk (Ideal.span {(ε : DualNumber A)})) M = 1 := by
  refine CommRing.Pic.eq_one_of_mapRingEquiv quotientSpanEpsRingEquiv ?_
  rw [CommRing.Pic.mapRingHom_mapRingHom, quotientSpanEpsRingEquiv_comp_mk]
  exact h

/-- **A `Pic A[ε]` class trivial along `ε ↦ 0` is trivial** — the algebraic content of clause
(iii-c2-aff), at the Picard group rather than at a module.

Three steps: restate along the ε-quotient (`pic_mapRingHom_mk_eq_one_of_fst`); read that as
freeness of the base change, the quotient map being the algebra map
(`mapRingHom_algebraMap` + `mapAlgebra_apply` + `mk_eq_one_iff_free`); then
`DualNumber.free_of_free_baseChange_eps`, which is `ReductionTrivialCyclic` composed with the
sibling-ported generator step and the nilpotent-Nakayama iteration.

No finiteness on the module, and nothing on `A` beyond commutativity — that generality comes from
the iteration in `Tangent/NilpotentThickeningFree.lean` and is preserved here. -/
theorem pic_eq_one_of_mapRingHom_fst (M : CommRing.Pic (DualNumber A))
    (h : CommRing.Pic.mapRingHom (fstRingHom (R := A)) M = 1) : M = 1 := by
  have hq := pic_mapRingHom_mk_eq_one_of_fst M h
  rw [← Ideal.Quotient.algebraMap_eq, CommRing.Pic.mapRingHom_algebraMap,
    CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free] at hq
  rw [← CommRing.Pic.mk_eq_self (M := M), CommRing.Pic.mk_eq_one_iff_free]
  exact DualNumber.free_of_free_baseChange_eps A M.AsModule hq

end TruncExpCech
