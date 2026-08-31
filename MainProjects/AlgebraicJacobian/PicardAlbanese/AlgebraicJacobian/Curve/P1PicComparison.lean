/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicEtUnitFieldComparison
import AlgebraicJacobian.Curve.P1Section
import AlgebraicJacobian.Curve.P1Curve
import AlgebraicJacobian.Curve.P1DegreeZeroTrivial
import AlgebraicJacobian.Curve.GeometricallyReduced

/-!
# The étale↔Zariski comparison of the relative Picard functor at `ℙ¹`, UNCONDITIONALLY

`Picard/PicEtUnitFieldComparison.lean` proves that over a **section-admitting** field test the
unit component `relPicToPicEt C (Spec K)` of the sheafification is a group isomorphism
`relPic C (Spec K) ≃* picEt C (Spec K)` (Kleiman 2.5, both parts), and its surjectivity
`relPicToPicEt_surjective_of_section`.  Both take a curve point
`σ : overSpec k K ⟶ C` as a hypothesis — the input inbox `I-1603` and the challenge-target
chain record as *constructed nowhere in the project*.

At `C = ℙ¹` that hypothesis is free.  `Curve/P1Section.lean` builds the canonical section
`P1.overSection k K : overSpec k K ⟶ (P1.asOver k)` (the origin `[1 : 0]`) over an arbitrary
test ring, in particular over every field extension `K/k`.  Feeding it to the comparison
discharges the `σ` binder, so at `ℙ¹` the comparison holds **with no hypothesis at all**:

* `P1.relPicToPicEt_surjective` — surjectivity of `relPicToPicEt (P1.asOver k) (overSpec k K)`,
  every field `K/k`;
* `P1.relPicToPicEtEquiv` — the group isomorphism `relPic ≃* picEt` at `ℙ¹` over `K`;
* `P1.relPicToPicEt_bijective` — the bijectivity corollary.

## The degree-zero part is trivial

`Curve/P1DegreeZeroTrivial.lean` proves a degree-zero Čech Picard class on `ℙ¹_K` is trivial
(`eq_one_of_classDeg_eq_zero_baseChange`, from `χ(𝒪) = 1`).  `RelPicDegree.lean`'s `relPicDeg K`
descends `classDeg K` to `relPic`, so the same fact reads on the relative Picard group:

* `P1.eq_one_of_relPicDeg_eq_zero` — a class of `relPic (ℙ¹_K)` with `relPicDeg K = 0` is `1`;
* `P1.eq_of_relPicDeg_eq` — the relative degree determines the class;
* `P1.relPicDeg_eq_zero_subsingleton` — two classes with `relPicDeg K = 0` are equal.

Transporting through the comparison isomorphism gives the same on the étale side:

* `P1.picEt_eq_one_of_relPicDeg_symm_eq_zero` — an étale class whose `relPic`-preimage has
  relative degree `0` is `1`.

## What this is for, and what it is NOT

This is the **field-side étale↔Zariski dictionary at `ℙ¹`**, with the section hypothesis
removed.  It is what the ring-case route (pic-c's Laurent computation of `relPic (ℙ¹_A)`, the
étale-plus honesty layer of `Picard/Pic0RingEngineFromPic0.lean`) consumes at each field point:
the comparison isomorphism is exactly the map along which a relPic computation transports to the
`picEt`/`pic0Subgroup` target the representability headline names.

It does **not** prove the ring case.  Over a general test ring `A` the effectivity half (C2) of
the comparison still uses field cofinality of étale covers
(`Algebra.EtaleCover.exists_finiteSeparableField_algHom`), which does not generalise; the
surjectivity of `relPicToPicEt` over a ring is the open content, orthogonal to seminormality
(the retraction of `I-1715`: the Traverso–Swan obstruction lives on the `𝔸¹` chart, not on
`ℙ¹_A`, and deg-`0` `relPic (ℙ¹_A)` is trivial unconditionally).  No new hypothesis is
introduced here: the three curve binders of `P1.asOver k` and `GeometricallyReduced` are all
`inferInstance`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace P1

variable (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]

/-! ## The comparison at `ℙ¹`, with the section hypothesis discharged -/

/-- **Surjectivity of the sheafification unit at `ℙ¹`, unconditionally.**  The section
hypothesis of `relPicToPicEt_surjective_of_section` is discharged by the canonical point
`P1.overSection k K`, so at `ℙ¹` every étale Picard class over a field test comes from an
honest relative Picard class — with no hypothesis on `K` beyond being a `k`-algebra field. -/
theorem relPicToPicEt_surjective :
    Function.Surjective (relPicToPicEt (P1.asOver k) (overSpec k K)) :=
  relPicToPicEt_surjective_of_section (P1.asOver k) K (P1.overSection k K)

/-- **The étale↔Zariski comparison isomorphism at `ℙ¹`**: the functor-level unit is a group
isomorphism `relPic (ℙ¹_K) ≃* picEt (ℙ¹_K)` over every field extension `K/k`, its section
hypothesis discharged by `P1.overSection`. -/
noncomputable def relPicToPicEtEquiv :
    relPic (P1.asOver k) (overSpec k K) ≃* picEt (P1.asOver k) (overSpec k K) :=
  relPicToPicEtEquiv_of_section (P1.asOver k) K (P1.overSection k K)

/-- The comparison isomorphism's underlying map is the honest unit `relPicToPicEt`. -/
@[simp]
theorem relPicToPicEtEquiv_apply (z : relPic (P1.asOver k) (overSpec k K)) :
    relPicToPicEtEquiv k K z = relPicToPicEt (P1.asOver k) (overSpec k K) z :=
  relPicToPicEtEquiv_of_section_apply (P1.asOver k) K (P1.overSection k K) z

/-- Bijectivity of the sheafification unit at `ℙ¹`, unconditionally. -/
theorem relPicToPicEt_bijective :
    Function.Bijective (relPicToPicEt (P1.asOver k) (overSpec k K)) :=
  relPicToPicEt_bijective_of_section (P1.asOver k) K (P1.overSection k K)

/-! ## The degree-zero part of the relative Picard group at `ℙ¹` is trivial -/

/-- **A relative Picard class on `ℙ¹_K` of relative degree zero is trivial.**  `relPicDeg K`
descends `classDeg K` along `relPicMk`, and a degree-zero Čech Picard class on `ℙ¹_K` is
trivial (`P1.eq_one_of_classDeg_eq_zero_baseChange`, from `χ(𝒪) = 1`). -/
theorem eq_one_of_relPicDeg_eq_zero (x : relPic (P1.asOver k) (overSpec k K))
    (hx : relPicDeg K x = 0) : x = 1 := by
  induction x using relPic.ind with
  | mk L =>
    rw [relPicDeg_relPicMk] at hx
    rw [P1.eq_one_of_classDeg_eq_zero_baseChange k K L hx]
    exact map_one _

/-- The degree determines a relative Picard class on `ℙ¹_K`: two classes of equal relative
degree are equal.  (`relPicDeg K` is injective on `relPic (ℙ¹_K)`.) -/
theorem eq_of_relPicDeg_eq (x y : relPic (P1.asOver k) (overSpec k K))
    (h : relPicDeg K x = relPicDeg K y) : x = y := by
  have hdiv : relPicDeg K (x * y⁻¹) = 0 := by
    rw [relPicDeg_mul, h, ← relPicDeg_mul, mul_inv_cancel, relPicDeg_one]
  have h1 : x * y⁻¹ = 1 := eq_one_of_relPicDeg_eq_zero k K _ hdiv
  exact mul_inv_eq_one.mp h1

/-- **The degree-zero relative Picard classes on `ℙ¹_K` form a subsingleton**: any two with
`relPicDeg K = 0` are equal (both are `1`). -/
theorem relPicDeg_eq_zero_subsingleton {x y : relPic (P1.asOver k) (overSpec k K)}
    (hx : relPicDeg K x = 0) (hy : relPicDeg K y = 0) : x = y := by
  rw [eq_one_of_relPicDeg_eq_zero k K x hx, eq_one_of_relPicDeg_eq_zero k K y hy]

/-! ## The same on the étale side, through the comparison isomorphism -/

/-- **An étale Picard class on `ℙ¹_K` whose relative preimage has relative degree zero is
trivial.**  Transports `eq_one_of_relPicDeg_eq_zero` along the comparison isomorphism
`relPicToPicEtEquiv`.  Every class of `picEt (ℙ¹_K)` has such a preimage because the comparison
is surjective (`relPicToPicEt_surjective`), so this is a genuine triviality criterion on the
étale side, not a conditional restatement. -/
theorem picEt_eq_one_of_relPicDeg_symm_eq_zero (w : picEt (P1.asOver k) (overSpec k K))
    (hw : relPicDeg K ((relPicToPicEtEquiv k K).symm w) = 0) : w = 1 := by
  have h1 : (relPicToPicEtEquiv k K).symm w = 1 := eq_one_of_relPicDeg_eq_zero k K _ hw
  have h2 := congrArg (relPicToPicEtEquiv k K) h1
  rwa [MulEquiv.apply_symm_apply, map_one] at h2

/-! ## The field-test `pic⁰` vanishing at `ℙ¹`, through the honest comparison

This is the shape the ring-case route must mirror: the degree-zero étale Picard group at `ℙ¹`
over a field is trivial, proved **through** the honest relative Picard group rather than around
it.  A `pic⁰` class pulls back to a `relPic` class along the surjection `relPicToPicEt`; that
preimage has relative degree zero (membership at the tautological point,
`relPicDeg_eq_zero_of_mem_pic0Subgroup`); and a degree-zero `relPic` class on `ℙ¹_K` is trivial.
So the whole vanishing rides on the two facts a ring-level computation of `Pic(ℙ¹_A)` would
supply — surjectivity of the unit and triviality of degree-zero `relPic` — with no separate
étale argument. -/

/-- **A degree-zero étale Picard class on `ℙ¹_K` is trivial**, via the honest comparison: it is
`relPicToPicEt` of a relative class whose relative degree vanishes, and degree-zero `relPic
(ℙ¹_K)` is trivial. -/
theorem pic0Subgroup_coe_eq_one (lam : pic0Subgroup (P1.asOver k) (overSpec k K)) :
    (lam : picEt (P1.asOver k) (overSpec k K)) = 1 := by
  obtain ⟨z, hz⟩ := relPicToPicEt_surjective k K (lam : picEt (P1.asOver k) (overSpec k K))
  have hzmem : relPicToPicEt (P1.asOver k) (overSpec k K) z
      ∈ pic0Subgroup (P1.asOver k) (overSpec k K) := hz ▸ lam.2
  have hdeg : relPicDeg K z = 0 :=
    relPicDeg_eq_zero_of_mem_pic0Subgroup (P1.asOver k) K hzmem
  rw [← hz, eq_one_of_relPicDeg_eq_zero k K z hdeg, map_one]

/-- **The degree-zero étale-sheafified Picard group of `ℙ¹` over a field is a subsingleton.**
The field-test instance of the `∀ T` binder both representability routes pass through, proved
through the honest relative Picard group (surjectivity of the comparison unit + triviality of
degree-zero `relPic`), the template the ring case is to reproduce.

**This conclusion already exists at HEAD** as `subsingleton_pic0Subgroup_overSpec_field`
(`Picard/Pic0VanishingFieldTest.lean`), proved through the `degAff` route; the two are
interderivable and this is **not new field-case mathematics**.  It is landed here as the
*route* the ring case must follow — surjectivity of `relPicToPicEt` and triviality of
degree-zero `relPic`, the two facts a ring-level `Pic(ℙ¹_A)` computation supplies — so that the
ring version transcribes this proof rather than the `degAff` one. -/
theorem subsingleton_pic0Subgroup :
    Subsingleton (pic0Subgroup (P1.asOver k) (overSpec k K)) :=
  ⟨fun s t => Subtype.ext ((pic0Subgroup_coe_eq_one k K s).trans
    (pic0Subgroup_coe_eq_one k K t).symm)⟩

end P1

end AlgebraicGeometry
