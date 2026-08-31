/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.DivRepAffPullClause

/-!
# U2 as an equation between morphisms: the chart maps lie in the range of the classifier

`Picard/DivRepAffPullClause.lean` reduced the whole divisor-representability chain to a
single hypothesis, `DivRepChartFamily.IsChartClause U`, and `IsChartClause.of_id` showed
that its `ω`-quantifier collapses to the identity point, i.e. to the DDR9-U ε-identity as
`informal/w4-ddr9-worksheet.md` §3.1 states it.  That is still a *submodule* identity with
a `∀`-quantifier over tower tests and framings hidden inside `IsDivRepClassify`.

This file removes that quantifier.  The backward classifier `divRepClassifyZar`
(`Picard/DivRepClassifyZar.lean`) is defined for **every** locally certified class over
**every** affine test, unconditionally, and `isDivRepClassify_unique` says it is the
*only* morphism satisfying the clause.  So the clause is not an extra property at all:

> `IsDivRepClassify F₀ v` ↔ `(divRepClassifyZar … F₀).left = v`.

Both directions are one line — forward is uniqueness, backward is a rewrite — and the
consequence is that U2 becomes an **equation between two morphisms of schemes that both
already exist**:

> U2 ↔ for each pair chart `(i, j)`, `(divRepClassifyZar … (U i j)).left = ChartMap i j`.

Reading off the existential, the last obligation of divisor representability is that
each chart map lies in the **range** of the classifier at its own chart ring:

> `divFunctor_representableBy_of_chartRange` :
>   `(∀ i j, ∃ F, (divRepClassifyZar … F).left = ChartMap i j) →`
>   `(divFunctor C π g).RepresentableBy DivOver`

Since `divRepClassifyZar` is injective on classes (`eq_of_isDivRepClassify`,
`Picard/DivRepClassifyZarSep.lean`), representability of `divFunctor` is *equivalent* to
surjectivity of `divRepClassifyZar` at every affine test; what this file records is that
surjectivity at the **chart rings alone** suffices.  That is the honest content: the
classifier is already a bijection onto its range everywhere, and the whole remaining debt
is that the finitely many chart points are hit.

## Main declarations

* `AlgebraicGeometry.isDivRepClassify_iff_divRepClassifyZar_left_eq` — the clause **is**
  the classifier equation, in both directions.  General: no chart family, no universal
  point.
* `AlgebraicGeometry.DivRepChartFamily.isChartClause_iff_forall_classify_eq` — U2 as a
  per-chart equation of morphisms, **as an iff**, so it is a reduction and not merely a
  restatement (the safeguard of inbox `I-0571`).
* `AlgebraicGeometry.divFunctor_representableBy_of_chartRange` — divisor
  representability from range membership of the chart maps.

## What this does NOT do

It produces no class over a chart ring, so it clears no gate: U2 is unproved and, per
roadmap `…divrep.u2`, the production of a chart class with the tautological ε remains the
G-4 obligation.  What changes is what a producer has to exhibit — a class whose classifier
*is* the chart map, rather than a family satisfying a quantified submodule identity.  The
endpoint also still carries `hO`, `hχ` and the ambient curve instances.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Grassmannian Scheme

section Curve

variable {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
variable {pi : C.left ⟶ P1 k} [IsFinite pi]

noncomputable local instance instOverCleftDivRepChartRange :
    C.left.Over (Spec (CommRingCat.of k)) := ⟨C.hom⟩

variable [SmoothOfRelativeDimension 1 (C.left ↘ Spec (CommRingCat.of k))]
  [IsIntegral C.left]
  [LocallyOfFiniteType (C.left ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (C.left ↘ Spec (CommRingCat.of k))]
  [IsDominant pi]
variable [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
  [GeometricallyIrreducible C.hom]
variable [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 0)]
  [Module.Finite k (Sheaf.HModule (C.left.moduleKSheaf k) 1)]
variable (hpi : pi ≫ P1.structureMap k = C.left ↘ Spec (CommRingCat.of k))
variable (g : ℕ)
variable (hO : Sheaf.h0 (C.left.moduleKSheaf k) = 1)
variable (hchi : Sheaf.chi (C.left.moduleKSheaf k) = 1 - (g : ℤ))
variable (r1 r2 : ℕ)
variable (b1 : Module.Basis (Fin r1) k
  ↥(divisorSections k (windowM_choice pi hpi g • fiberWeilDivisor pi) ⊤))
variable (b2 : Module.Basis (Fin r2) k
  ↥(divisorSections k
    ((windowM_choice pi hpi g + windowS_choice pi hpi g) • fiberWeilDivisor pi) ⊤))

local notation "DivOver" =>
  divSchemeOver k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm)

local notation "ChartRing" => fun i j =>
  DivCarveChartRing k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

local notation "ChartMap" => fun i j =>
  divCarveChartToDivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
    (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
    (b2.map (windowShiftEquiv hpi g).symm) i j

/-! ## `Spec` of an identity algebra map -/

/-- `Spec` of the identity `k`-algebra map is the identity morphism.

Stated for an abstract algebra `A` on purpose.  At `A := DivCarveChartRing …` the same
step inside a tactic block does not elaborate: the rewrite pattern of
`AlgHom.id_toRingHom` is stated through the `RingHom` coercion, and matching it against
the chart ring's `Ideal.Quotient` type forces the elaborator to unfold the quotient while
`glueData`'s `ULift` index is still being unified (recorded hazard).  Abstracting the
algebra keeps the rewrite at the level where the named lemmas apply. -/
theorem specMap_ofHom_algHom_id (A : Type u) [CommRing A] [Algebra k A] :
    Spec.map (CommRingCat.ofHom (AlgHom.id k A).toRingHom)
      = CategoryStruct.id (Spec (CommRingCat.of A)) := by
  have hid : (AlgHom.id k A).toRingHom = RingHom.id A := rfl
  rw [hid, CommRingCat.ofHom_id, Spec.map_id]

/-! ## The clause is the classifier equation -/

include hO hchi in
/-- **`IsDivRepClassify` is an equation, not a property.**  The backward classifier
`divRepClassifyZar` is defined for every locally certified class over every affine test,
and `isDivRepClassify_unique` makes it the *unique* morphism satisfying the characterizing
clause.  So a morphism satisfies the clause for `F₀` exactly when it **is** the classifier
of `F₀`.

Forward is uniqueness against `divRepClassifyZar_isDivRepClassify`; backward is a rewrite.
Mentioning no chart family and no universal point, this is what turns the DDR9-U
ε-identity into an equation between two already-existing morphisms of schemes (see
`DivRepChartFamily.isChartClause_iff_forall_classify_eq`). -/
theorem isDivRepClassify_iff_divRepClassifyZar_left_eq {S : Type u} [CommRing S]
    [Algebra k S] (F₀ : DivFamZar C S pi g)
    (v : Spec (CommRingCat.of S) ⟶
      DivScheme k (windowS_choice pi hpi g • fiberWeilDivisor pi)
        (windowM_choice pi hpi g • fiberWeilDivisor pi) g r1 r2 b1
        (b2.map (windowShiftEquiv hpi g).symm)) :
    IsDivRepClassify hpi g r1 r2 b1 b2 F₀ v ↔
      (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 S F₀).left = v := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · exact isDivRepClassify_unique hpi g hO hchi r1 r2 b1 b2 F₀
      (divRepClassifyZar_isDivRepClassify hpi g hO hchi r1 r2 b1 b2 F₀) hv
  · rw [← hv]
    exact divRepClassifyZar_isDivRepClassify hpi g hO hchi r1 r2 b1 b2 F₀

/-! ## U2 as a per-chart equation of morphisms -/

namespace DivRepChartFamily

set_option maxHeartbeats 1600000 in
-- Both directions instantiate `IsDivRepClassify` at the chart ring, whose `DivCarveChartRing`
-- quotient type the elaborator unfolds while unifying `divRepPullAt`'s `mapAlgHom`; the same
-- defeq profile as `IsChartClause.of_id`, which is budgeted identically.
include hO hchi in
/-- **U2, as an equation between morphisms** — and an **iff**, so it is a reduction of the
obligation rather than a restatement of it (the safeguard of inbox `I-0571`).

`IsChartClause U` holds exactly when, for each pair chart `(i, j)`, the backward
classifier of the supplied chart class *is* that chart's own map to `DivScheme`.  The
`ω`-quantifier collapses by `IsChartClause.of_id`, and the clause at the identity point is
the classifier equation by `isDivRepClassify_iff_divRepClassifyZar_left_eq`.

So the DDR9-U ε-identity carries no residual quantifier over tower tests or framings: what
a producer owes is that two morphisms `Spec R_Z(i,j) ⟶ DivScheme g`, both of which already
exist unconditionally, agree. -/
theorem isChartClause_iff_forall_classify_eq
    (U : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      DivFamZar C (ChartRing i j) pi g) :
    IsChartClause (hpi := hpi) g r1 r2 b1 b2 U ↔
      ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
        (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 (ChartRing i j) (U i j)).left
          = ChartMap i j := by
  refine ⟨fun hU i j => ?_, fun hU => IsChartClause.of_id hpi g r1 r2 b1 b2 fun i j => ?_⟩
  · -- instantiate the clause at the identity point of the chart
    have h := hU (S := ChartRing i j) i j (AlgHom.id k (ChartRing i j))
    rw [divRepPullAt_id] at h
    -- `Spec` of the identity algebra map is the identity; the rewrite is done at an
    -- ABSTRACT algebra (`specMap_ofHom_algHom_id`) because the same step spelled inline
    -- against the chart ring's quotient type does not elaborate.
    rw [specMap_ofHom_algHom_id (k := k), Category.id_comp] at h
    exact (isDivRepClassify_iff_divRepClassifyZar_left_eq hpi g hO hchi r1 r2 b1 b2
      (U i j) (ChartMap i j)).mp h
  · exact (isDivRepClassify_iff_divRepClassifyZar_left_eq hpi g hO hchi r1 r2 b1 b2
      (U i j) (ChartMap i j)).mpr (hU i j)

end DivRepChartFamily

/-! ## Representability from range membership -/

include hO hchi in
/-- **Divisor representability from range membership of the chart maps** — the form this
file exists to state.

`divRepClassifyZar` is injective on classes (`eq_of_isDivRepClassify`), so representability
of `divFunctor` is *equivalent* to the classifier being surjective at every affine test.
This says surjectivity at the **chart rings alone** suffices: if each chart map
`ChartMap i j` is the classifier of *some* locally certified class over its own chart ring
`R_Z(i,j)`, then `divFunctor C π g` is represented by `divSchemeOver`.

Nothing here produces such a class; per roadmap `…divrep.u2` that is the G-4 obligation.
The value is the shape of what is owed: a *preimage under a landed map*, at
`glueData`-many points, rather than a quantified submodule identity. -/
noncomputable def divFunctor_representableBy_of_chartRange
    (hrange : ∀ (i : (glueData k g r1).J) (j : (glueData k g r2).J),
      ∃ F : DivFamZar C (ChartRing i j) pi g,
        (divRepClassifyZar hpi g hO hchi r1 r2 b1 b2 (ChartRing i j) F).left
          = ChartMap i j) :
    (divFunctor C pi g).RepresentableBy DivOver :=
  divFunctor_representableBy_of_chartClause hpi g hO hchi r1 r2 b1 b2
    (fun i j => (hrange i j).choose)
    ((DivRepChartFamily.isChartClause_iff_forall_classify_eq hpi g hO hchi r1 r2 b1 b2
      (fun i j => (hrange i j).choose)).mpr (fun i j => (hrange i j).choose_spec))

end Curve

end AlgebraicGeometry
