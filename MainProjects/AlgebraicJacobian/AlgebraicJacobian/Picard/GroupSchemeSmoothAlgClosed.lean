/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Smoothness of a group scheme from reducedness over ONE algebraic closure

Mathlib's `AlgebraicGeometry.smooth_of_grpObj` proves that a group scheme locally of finite
type over a field is smooth as soon as it is **geometrically** reduced, i.e. as soon as
`X ×_k Spec K` is reduced for *every* field `K` and every `Spec K ⟶ Spec k`. Internally it
goes through a `private` lemma which needs only reducedness of the **single** base change to
the algebraic closure — the geometric content is the translation argument at an algebraically
closed base, and the general field case is obtained by flat descent along `Spec k̄ → Spec k`.

That `private` modifier is the whole reason for this file. Both this project and the sibling
`Algebraic-Jacobian-Challenge-Rebuild` reached the same conclusion independently (inbox
I-0495, 2026-07-28): the smoothness leg of "`Pic⁰_{C/k}` is an abelian variety" wants to
supply reducedness over `k̄` and nothing more, because

* `Algebra.IsGeometricallyReduced` is *defined* by base change to an algebraic closure
  (`Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`), so at the algebra level the
  k̄-statement is the definition rather than a special case;
* the scheme-level class `GeometricallyReduced` quantifies over all field base changes, and
  the passage from the `k̄` case to that quantifier is **absent from mathlib v4.31** — it is
  the transcendental half of `IsReduced after base change to k̄ ⟹ GeometricallyReduced`,
  which has no producer in mathlib and no `MorphismProperty.DescendsAlong` instance either
  (verified by machine on both sides, recorded on inbox I-0495).

So the honest input to smoothness is the `k̄` one, and the cross-project thread priced getting
it as *an upstream PR making `smooth_of_grpObj_of_isAlgClosed` public*. It is cheaper than
that: the `private` proof uses only public API, so it can simply be re-derived here. This
file does that and then packages the descent step, giving a smoothness criterion whose
hypothesis is a single `IsReduced`.

## Main results

* `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed'` — the re-derivation of mathlib's
  `private` lemma: a reduced group scheme locally of finite type over an algebraically closed
  field is smooth. Proof transcribed from `Mathlib/AlgebraicGeometry/Group/Smooth.lean`
  (Andrew Yang), which is why the `set_option`s and the `open`s are the same.
* `AlgebraicGeometry.smooth_of_grpObj_of_isReduced_algebraicClosureBaseChange` — the
  criterion this project actually consumes: `G ⟶ Spec k` is smooth as soon as the base change
  `G ×_{Spec k} Spec k̄` is reduced. No `GeometricallyReduced`, no quantifier over fields.

## Change of attack surface, NOT of strength — corrected after review

An earlier version of this docstring called the criterion's hypothesis **strictly weaker** than
`smooth_of_grpObj`'s. **That is wrong in this project, and the correction is the interesting
part.** Fresh-context review (run 0067) established:

* in **mathlib alone**, `IsReduced`-over-`k̄ ⟹ GeometricallyReduced` is indeed unavailable —
  `infer_instance` fails for it on a bare `import Mathlib`;
* but **this project owns the converse**: `Smooth.geometricallyReduced`
  (`AlgebraicJacobian/Curve/GeometricallyReduced.lean`, an instance) derives the class from
  smoothness. So `IsReduced`-over-`k̄` → (this criterion) → `Smooth` → `GeometricallyReduced`
  closes by `inferInstance`, axiom-clean.

At these binders the two hypotheses are therefore **interprovable**, and this file is a
restatement rather than a weakening. The mistake was methodological and worth recording: the
"missing in mathlib" measurement was taken inside the *edited file's* import cone (99 modules),
which does not contain `Curve/GeometricallyReduced`, while the root cone (215 modules) does.
A synthesis probe cannot see a bridge its own imports exclude — measure at the root.

**What the restatement is still good for**, which is why it stays: the two hypotheses are
equivalent but not equally *attackable*. `GeometricallyReduced` quantifies over every field
extension and has no producer here other than the circular one; reducedness of one scheme over
one algebraically closed field is where Kleiman §5's argument (and Cartier's theorem in
characteristic zero) actually speaks. Same strength, better attack surface.

**And the corollary the first version missed**: since the criterion yields `Smooth` and
`Smooth.geometricallyReduced` yields the class, the `k̄` hypothesis discharges
`Pic0.geometricallyReduced` — an open `sorry` of `Picard/Pic0AbelianVariety.lean` — as well as
the smoothness leg. One statement, two obligations. Verified axiom-clean at the root; see
`Pic0.geometricallyReduced_of_isReduced_algebraicClosureBaseChange` there.

## References

Mathlib `AlgebraicGeometry/Group/Smooth.lean`; Kleiman, "The Picard scheme"
(arXiv:math/0504020), §5. Cross-project analysis: inbox I-0495 (2026-07-28).
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {G : Scheme.{u}} (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open MonObj MonoidalCategory CartesianMonoidalCategory in
/-- **A reduced group scheme locally of finite type over an algebraically closed field is
smooth** — the re-derivation of mathlib's `private smooth_of_grpObj_of_isAlgClosed`.

The mathematics is not ours: the proof below is transcribed from
`Mathlib/AlgebraicGeometry/Group/Smooth.lean` (Andrew Yang), which is why the `set_option`s,
the `open`s and the tactic script agree with it line for line. It is re-derived rather than
imported because the mathlib declaration is `private`, and its statement — reducedness over
*one* algebraically closed field — is the hypothesis this project can actually supply, while
the public `smooth_of_grpObj` asks for the full `GeometricallyReduced` class.

The argument itself: the smooth locus is nonempty (generic smoothness over a perfect field)
and stable under the translation isomorphisms `GrpObj.mulRight`, which act transitively on
closed points; a Jacobson space whose points are closed-point-dense then forces the smooth
locus to be everything. -/
theorem smooth_of_grpObj_of_isAlgClosed' [IsReduced G] [IsAlgClosed K] : Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty G := ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    (GrpObj.mulRight (A := Over.mk f) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using congr(($hα).left (IsLocalRing.closedPoint K))
  rw! [← hα', ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy

/-- **Smoothness of a group scheme from reducedness of the base change to `k̄` alone.**

The criterion this project consumes in place of `smooth_of_grpObj`: for `G` a `k`-group
scheme locally of finite type, `G ⟶ Spec k` is smooth as soon as the single scheme
`G ×_{Spec k} Spec k̄` is reduced. There is no `GeometricallyReduced` hypothesis and no
quantifier over field extensions.

The descent step is mathlib's, verbatim from `smooth_of_grpObj`:
`MorphismProperty.of_pullback_snd_of_descendsAlong` against
`@Surjective ⊓ @Flat ⊓ @QuasiCompact`, along which `@Smooth` descends
(`Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean`). The group structure transports
to the base change by `Over.grpObjMkPullbackSnd`. What changes is only *where the reducedness
hypothesis is taken*: `smooth_of_grpObj` derives `IsReduced` of the pullback from the
`GeometricallyReduced` instance, whereas here it is supplied directly.

Same strength, different attack surface — **not** a weaker hypothesis. In mathlib alone the
converse (`IsReduced` over `k̄` ⟹ `GeometricallyReduced`) is unavailable, but this project owns
it through `Smooth.geometricallyReduced`, so at these binders the two are interprovable. See
the module docstring for the correction and for why the restatement is still worth having. -/
theorem smooth_of_grpObj_of_isReduced_algebraicClosureBaseChange
    (h : IsReduced (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))) :
    Smooth f := by
  let Ω : Type u := AlgebraicClosure K
  let g : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom <| algebraMap K Ω)
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := g)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · letI : GrpObj (Over.mk (Limits.pullback.snd f g)) := Over.grpObjMkPullbackSnd
    haveI := h
    exact smooth_of_grpObj_of_isAlgClosed' _

end AlgebraicGeometry
