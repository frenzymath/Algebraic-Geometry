/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.Pic0ChartLocus

/-!
# The unconditional splitting of a plus class over a field (CHART-U(a), input 1)

`informal/w4-datb-worksheet.md` §1.2 step 1 and `informal/w4-datc-worksheet.md` §3.3 both
open with the same move, and both treat it as a step of a longer argument:

> restrict along `t`; a plus class over `κ(t)` is `PicEtAff.mk E x`; étale field-cofinality
> produces a finite separable `L/κ(t)` over which the class is an honest Čech class.

This file makes that move a **named, unconditional theorem** rather than a step, because it
is consumed at three separate places (the split predicate `IsSplitWitness`, the coverage
theorem COV-1, and the degree seam) and because its statement is exactly the *witness-free*
half of `IsSplitWitness`: every plus class over a field becomes an honest Čech class over
some finite separable extension.  Nothing here mentions a witness divisor, `H¹`, `θ`, `Σ`,
`divRep` or a certificate.

## Why this is worth isolating

`IsSplitWitness C μ` (`Picard/Pic0ChartLocus.lean:148`) is an existential over a *tuple*: the
extension `L`, its four instances, the presenting Čech class `M`, and then the witness
divisor.  Read naively, a consumer proving membership of `chartLocus` has to produce all of
them at once, and a consumer *using* membership has to destructure all of them.  But the
first six components exist for **every** class, with no hypothesis at all — that is
`exists_splitting_of_picEt` below.  So the honest content of `IsSplitWitness` is only the
witness clause *at* a splitting, and the two readings are related by
`isSplitWitness_iff_exists_splitting_witness`.

That matters for the lane order: COV-1 (dat-b §1.2) can produce its splitting *before* it
knows anything about `h⁰`/`h¹`, choose `m` at that field (§1.2 step 3, where the uniform
bound genuinely does not exist), and only then run the drop.  Without this separation the
`m`-choice and the splitting choice are entangled inside one `∃`.

## Main declarations

* `AlgebraicGeometry.exists_splitting_of_picEtAff` — **every plus class over a field is an
  honest Čech class over some finite separable extension.**  Unconditional; no witness.
* `AlgebraicGeometry.exists_splitting_of_picEt` — the same in the `picEt` spelling, which is
  the one `IsSplitWitness` is stated against.
* `AlgebraicGeometry.isSplitWitness_iff_exists_splitting_witness` — the two readings agree:
  `IsSplitWitness` is exactly "some splitting carries a witness".  Its `.mpr` is also the
  introduction rule; see the closing note for why no positional constructor lemma exists.
-/

set_option autoImplicit false
/- Statements mix `relCurve C L` with the product spelling `(C ⊗ overSpec k L).left`. -/
set_option backward.isDefEq.respectTransparency false
/- `lake env lean` drops the lakefile's `[leanOptions]` (I-0161). -/
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace Opposite

namespace AlgebraicGeometry

open AlgebraicJacobian

attribute [local instance] Scheme.overModule Scheme.overSectionsAlgebra
attribute [local instance 10000] relCurve.instOver

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

noncomputable section

/-! ## The splitting itself -/

set_option maxHeartbeats 1600000 in
-- The presentation lives over the base-changed étale carrier, and closing the existential
-- unifies its `Algebra k L` (the derived composite) against the goal's through that carrier
-- — the same heavy defeq `PicEtAffFieldCollapse.lean` budgets 800000 for.
/-- **Every plus class over a field is an honest Čech class over some finite separable
extension** (`w4-datb` §1.2 step 1, `w4-datc` §3.3 — the first move of both, here
unconditional and witness-free).

Given `μ : picEt C (overSpec k K)`, there is a finite separable `L/K` and a Čech Picard
class `M` on `C_L` with `μ|_L = relPicMk M` as plus classes.

The three steps, each a landed brick:

1. `picEtAffineEquiv` (`Picard/PicEt.lean:235`) reads `μ` in `PicEtAff C K`, where by
   `PicEtAff.ind` it is `PicEtAff.mk E x` for a presented étale cover `E` of `K` and a
   descent class `x`;
2. étale field-cofinality — `Algebra.EtaleCover.exists_finiteSeparableField_algHom`
   (`Algebra/EtaleCover.lean:287`) — refines `E` by a finite separable field `L/K`,
   i.e. supplies `ℓ : E.Carrier →ₐ[K] L`.  This is the step that uses that `K` is a
   *field*: over a general base an étale cover has no such refinement;
3. `PicEtAff.map_mk_eq_unit_relPicMk_of_algHom` (`Picard/PicEtAffFieldCollapse.lean:101`)
   converts the refinement into the presentation.

The `k`-algebra structure on `L` and the tower `k → K → L` are *derived*, not chosen: they
are the composite `algebraMap K L ∘ algebraMap k K`, exactly as `degAffFieldAlgebraBase`
(`Picard/DegreeZero.lean:229`) does it.  Constructing them here rather than demanding them
of the caller is the whole ergonomic point — a caller who has only `K` cannot produce them,
since `L` does not exist until step 2. -/
theorem exists_splitting_of_picEtAff (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    {K : Type u} [Field K] [Algebra k K]
    (a : PicEtAff C K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
        (M : ((C ⊗ overSpec k L).left).CechPic),
      PicEtAff.map C L a = PicEtAff.unit C L (relPicMk C (overSpec k L) M) := by
  -- (1) read `a` as a plus class on a presented cover
  induction a using PicEtAff.ind with
  | mk E x =>
    -- (2) refine the cover by a finite separable field
    obtain ⟨L, hLfield, hLalg, hLfin, hLsep, ⟨ℓ⟩⟩ := E.exists_finiteSeparableField_algHom
    letI := hLfield
    letI := hLalg
    letI := hLfin
    letI := hLsep
    -- the `k`-structure and the tower are the composite, not a choice
    letI hkL : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    haveI htow : IsScalarTower k K L := .of_algebraMap_eq fun _ => rfl
    -- FORGET the composite's VALUE before going further (I-0161-adjacent hazard, measured
    -- this session).  Keeping it transparent makes the final `exact` substitute a composite
    -- algebra term for the existential's variable, and every `overSpec k L` /
    -- `(C ⊗ overSpec k L).left` in the goal is then rechecked against a differently-spelled
    -- instance — that defeq does not terminate inside 1600000 heartbeats.  `htow` is a
    -- `have`, so it has already forgotten the value it was proved from; nothing downstream
    -- needs it.
    clear_value hkL
    -- (3) the refinement is the presentation
    obtain ⟨M, hM⟩ := PicEtAff.map_mk_eq_unit_relPicMk_of_algHom C x ℓ
    exact ⟨L, hLfield, hkL, hLalg, htow, hLfin, hLsep, M, hM⟩

variable (C) in
/-- **The splitting theorem in the `picEt` spelling** — the form every consumer of
`IsSplitWitness` meets, since the split predicate is stated on
`PicEtAff.map C L (picEtAffineEquiv C K μ)`.  Immediate from
`exists_splitting_of_picEtAff` at `a := picEtAffineEquiv C K μ`; kept separate so that the
heavy elaboration of the previous theorem is not re-run through the affine comparison. -/
theorem exists_splitting_of_picEt {K : Type u} [Field K] [Algebra k K]
    (μ : picEt C (overSpec k K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
        (_ : IsScalarTower k K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
        (M : ((C ⊗ overSpec k L).left).CechPic),
      PicEtAff.map C L (picEtAffineEquiv C K μ)
        = PicEtAff.unit C L (relPicMk C (overSpec k L) M) :=
  exists_splitting_of_picEtAff C (picEtAffineEquiv C K μ)

/-! ## The two readings of `IsSplitWitness` -/

variable (C) in
/-- **`IsSplitWitness` is exactly "some splitting carries a witness"** — the two readings of
the (a-amendment) agree.

The forward direction is destructuring.  The reverse is `isSplitWitness_of_splitting`.  The
point of stating it as an `iff` is that the *left* side is the definition consumers meet and
the *right* side separates the two independent choices (which extension; which witness),
which is what makes the COV-1 lane order of `w4-datb` §1.2 legal: the splitting is fixed at
step 1, the witness only at step 5. -/
theorem isSplitWitness_iff_exists_splitting_witness {K : Type u} [Field K] [Algebra k K]
    (μ : picEt C (overSpec k K)) :
    IsSplitWitness C μ
      ↔ ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra K L)
          (_ : IsScalarTower k K L) (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L)
          (M : (relCurve C L).CechPic),
        (PicEtAff.map C L (picEtAffineEquiv C K μ)
            = PicEtAff.unit C L (relPicMk C (overSpec k L) M))
          ∧ ∃ W : ((C ⊗ overSpec k L).left).CurveDivisor,
              Scheme.CurveDivisor.picClass L W = M
                ∧ Subsingleton (Sheaf.HModule
                    ((C ⊗ overSpec k L).left.divisorSheaf L W) 1) :=
  Iff.rfl

/-! ## A note on the intro rule — SUPERSEDED, and the correction matters

**The intro rule EXISTS.** It is `isSplitWitness_of_presenting_witness`
(`Picard/Pic0ChartTwistSplit.lean`), it elaborates at the default heartbeat budget, and its
`L := K` case — the one this note's earlier version called out as wanted but unreachable — is
a one-liner there.  Read that theorem's docstring, not this paragraph, for the current state.

What this note originally recorded, and what remains TRUE: an `isSplitWitness_of_splitting`
handing all twelve components to **one anonymous constructor** does not elaborate.
`IsSplitWitness` mixes the two spellings of the base-changed curve —
`(relCurve C L).CechPic` for the presenting class, `((C ⊗ overSpec k L).left).CurveDivisor` for
the witness divisor — so a single tuple makes Lean unify the seven instance slots *while `L` is
still a metavariable*, re-checking those carriers on each attempted assignment.  `refine`
instead of `exact`, pre-bundling the witness clause, normalising either spelling, and routing
through the `iff` are all the same shape, and all of them time out.

What it got wrong was the conclusion drawn from that: it read "the tuple is too expensive" as
"there is no introduction rule", and proposed restating `IsSplitWitness` with one spelling —
a refactor of a definition co-signed in `w4-datb` §1.6.  The actual fix is tactic-level:
**stage the existentials.**  Eight `refine Exists.intro x ?_`s fix `L` at the first step, after
which every later component is checked against a closed type and the two spellings never race.

So the corrected rule is not "prefer `Iff.rfl` plus `.mpr`" but: *a deep existential over
types-carrying-instances must have its intros staged, not bundled.*  The diagnosis above is
not refuted by this — it is precisely why staging works. -/

end

end AlgebraicGeometry
