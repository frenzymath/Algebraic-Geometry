/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowTensorAction

/-!
# The invariants as a limit **over the base**: closing the category mismatch

`Albanese/SymPowInvariants.lean` proved that the invariant subring is the limit of a group
action — in `CommRingCat`, with no base ring. Its §4 then flagged, as the third of three open
items, that this is **the wrong category** for the consumer:

> **The category.** `SymPowColimit`'s affine statement is over `(Under k)ᵒᵖ`; everything here
> is over `CommRingCatᵒᵖ`. No declaration bridges them, so nothing in that file can consume
> anything in this one.

That item is closed here, and closed by *restating rather than bridging* — which turned out
to be the cheaper route. Rather than transporting the `CommRingCat` limit across
`Over.opEquivOpUnder`, the cone is rebuilt directly in `Under k`: the invariant
**subalgebra** `A^G` is already a `k`-algebra, so it is an object of `Under k` on the nose,
and the limit proof is the `CommRingCat` one with `(Under.forget k).map_injective` inserted
before each `hom_ext`. No transport, no `eqToHom`, no defeq wall.

## Main results

* `actionDiagramUnder` — the action as a diagram in `Under k`. Well-defined exactly because
  the action fixes the base: that is `[SMulCommClass G k A]`, and the proof is
  `algebraMap r = r • 1` followed by `smul_comm`.
* `fixedUnder` — `A^G` as an object of `Under k`, i.e. as a `k`-algebra.
* `fixedConeUnderIsLimit` — **the identification over the base**: the cone with vertex `A^G`
  is a limit cone in `Under k`.
* `hasLimit_actionDiagramUnder`, `fixedCoconeUnderIsColimitOp`,
  `hasColimit_actionDiagramUnder_op` — the `HasLimit` form and the dual, in `(Under k)ᵒᵖ`,
  which is the variance and the category of `SymPowColimit.symPowData_affineAlgebra`.
* `hasColimit_actionDiagramUnder_op_symTensorPow` — the whole stack at Milne's ring: the
  `S_n`-action on `A^{⊗ n}` from `SymPowTensorAction`, quotiented over `k`.
* `hasColimit_singleObj_of_op` / `invEquivalence_comp_op_map` — the **index-category** step,
  which an earlier draft of this file wrongly treated as absent: `Functor.op` gives a diagram
  over `(SingleObj G)ᵒᵖ`, not over `SingleObj G`, and the transport is `Groupoid.invEquivalence`
  with the reindexing being `σ ↦ σ⁻¹` on the nose.

## What the hypothesis `[SMulCommClass G k A]` is, and why it is not a weakening

`SymPowInvariants` assumed nothing beyond a `MulSemiringAction`. Over a base one must assume
the action is `k`-linear, otherwise the action maps are not morphisms of `Under k` and the
diagram does not exist. `SMulCommClass G k A` says exactly `g • (r • a) = r • (g • a)`, and
for Milne's case it holds: `permAlgHom` is an `R`-*algebra* hom by construction, so `R`-linear
by `map_smul`. That instance is supplied below (`permSMulCommClass`) rather than assumed.

## Scope

This closes the *category* item only. Still open, and untouched here:

* **the gluing** — `HasColimit (permDiagram C g)` in `Over (Spec k̄)` for the proper curve.
  `SymPowColimit.lean` §6 has the availability table; the affine charts now have a carrier
  over the base, which is what a `Scheme.GlueData` comparison on overlaps would need, but no
  glue data is built here.
* Consequently `AlbaneseUP.lean`'s six sorries are **unchanged**, and
  `albanese_universal_property` still reports `sorryAx`. Nothing below is a statement about
  `Sym^g C` for a curve.

Two honest notes on consumption, since this lane has twice recorded claiming a gap closed
without a consumer (inbox `I-0571`, `I-0637`).

**First**, no declaration in `SymPowColimit.lean` has been *rewritten* to consume
`hasColimit_actionDiagramUnder_op`; `grep` finds zero consumers of the names below. What
changed is that the obstruction is no longer a category mismatch.

**Second — and this is a correction to a claim an earlier draft of this header made.** "Same
category, same variance" is not enough, for **two** further reasons. A reviewer found both;
one was in the draft and one the draft missed entirely.

*(a) The index category.* `Functor.op` produces a diagram indexed by `(SingleObj G)ᵒᵖ`, while
`SymPowColimit.permDiagram` is indexed by `SingleObj (Equiv.Perm (Fin n))`. §5 handles that
with `hasColimit_singleObj_of_op`, transporting along `Groupoid.invEquivalence`, and records
that the reindexing is exactly the `σ ↦ σ⁻¹` convention already carried twice elsewhere in
this cone. (That lemma was first stated with all universes pinned to `u`, which excluded
`Under k` — `Category.{u, u+1}` — so it was true and inapplicable at the one category the leg
needs. Fixed to `{C : Type w} [Category.{v} C]`, same proof.)

*(b) The **object**, and this is the one that actually blocks consumption.*
`symPowData_affineAlgebra` builds `permDiagram X n` from the `n`-fold *product of `X` in
`(Under k)ᵒᵖ`*, i.e. the `n`-fold *coproduct in `Under k`*. Everything here is about
`⨂[k] _ : Fin n, A`. For those to be the same object one needs (i) the `n`-ary coproduct of
`k`-algebras identified with the `n`-fold tensor power and (ii) the induced permutation action
matched to `PiTensorProduct.permAlgHom`.

**Updated 2026-07-29 (run 0069 r6): (i) and (ii) now exist; the paragraph above said "neither
exists" and that is no longer true.** `Albanese/TensorPowerCoproduct.lean` supplies the `n`-ary
universal property (`existsUnique_coprodLift`) together with both equivariance statements
(`coprodLift_permAlgHom` and `permAlgHom_comp_singleAlgHom`). The claim that mathlib has only
the binary case was itself the error: mathlib has both halves of the `n`-ary property
unbundled — uniqueness *is* `PiTensorProduct.algHom_ext`, existence is one `liftAlgHom` — and
only the binary *pushout* is packaged as a colimit, which is what the comparison was made
against.

What still blocks literal consumption is narrower than a missing brick: the `Cofan`/`IsColimit`
packaging in `(Under k)ᵒᵖ` has not been written, so `symPowData_affineAlgebra`'s diagram and
this file's carrier remain formally distinct even though the mathematics identifying them is
proved. Calling these statements "directly consumable" would still be an overclaim — but the
remaining step is categorical bookkeeping, not mathematics.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94. Consumers: this file's carrier is
the affine chart of `Albanese/SymPowColimit.lean` §5.
-/

set_option autoImplicit false

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

section UnderInvariants

variable (k : CommRingCat.{u}) (G : Type u) [Group G] (A : Type u)
    [CommRing A] [Algebra k A] [MulSemiringAction G A] [SMulCommClass G k A]

/-! ## §1. The action as a diagram over the base

The only new content relative to `SymPowInvariants.actionDiagram` is the triangle: each
action map must commute with the structure morphism `k ⟶ A`. That is where
`[SMulCommClass G k A]` is spent, and it is spent once. -/

/-- **A `k`-linear ring action, as a one-object diagram in `Under k`.**

Same construction as `SymPowInvariants.actionDiagram`, but in the over-category: the
structure-map triangle holds because `algebraMap r = r • 1` and the action commutes with
scalars. -/
noncomputable def actionDiagramUnder : SingleObj G ⥤ Under k :=
  SingleObj.functor (M := G) (X := Under.mk (CommRingCat.ofHom (algebraMap k A)))
    { toFun := fun g => Under.homMk (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g))
          (by
            apply CommRingCat.hom_ext
            ext r
            change g • (algebraMap k A r) = algebraMap k A r
            rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one])
      map_one' := by
        apply (Under.forget k).map_injective
        apply CommRingCat.hom_ext
        ext (x : A)
        change (1 : G) • x = x
        rw [one_smul]
      map_mul' := by
        intro g h
        apply (Under.forget k).map_injective
        apply CommRingCat.hom_ext
        ext (x : A)
        change (g * h) • x = g • h • x
        rw [mul_smul] }

/-- **`A^G` as a `k`-algebra**, i.e. as an object of `Under k`. Mathlib's
`FixedPoints.subalgebra` already *is* a `k`-subalgebra — this is only its packaging as an
`Under k` object, and it is why no transport across `Over.opEquivOpUnder` is needed. -/
noncomputable def fixedUnder : Under k :=
  Under.mk (CommRingCat.ofHom (R := k) (S := FixedPoints.subalgebra k A G)
    (algebraMap k (FixedPoints.subalgebra k A G)))

/-! ## §2. The invariants are the limit, over the base

The proof is `SymPowInvariants.fixedConeIsLimit` with one insertion: a morphism of `Under k`
is determined by its underlying ring map, so each `hom_ext` is preceded by
`(Under.forget k).map_injective`. The cone condition and the lift are unchanged — an element
of the vertex lands in the invariants *because* the cone condition says its image is fixed. -/

/-- **The cone over the action with vertex `A^G`, over the base.** -/
noncomputable def fixedConeUnder : Cone (actionDiagramUnder k G A) where
  pt := fixedUnder k G A
  π :=
    { app := fun _ => Under.homMk
        (CommRingCat.ofHom (R := FixedPoints.subalgebra k A G) (S := A)
          (FixedPoints.subalgebra k A G).subtype) (by
          apply CommRingCat.hom_ext; ext r; rfl)
      naturality := by
        intro X Y f
        apply (Under.forget k).map_injective
        apply CommRingCat.hom_ext
        ext (x : FixedPoints.subalgebra k A G)
        change ((x : A)) = (f : G) • (x : A)
        exact (x.2 _).symm }

/-- **The identification over the base: `A^G` IS the limit in `Under k`.**

This is the statement `SymPowInvariants` §4's third item asked for — same category as
`SymPowColimit.symPowData_affineAlgebra`, so a consumer there could take it, which nothing
could do with the `CommRingCat` version.

The `lift`'s triangle obligation is the only step with no counterpart in the base-free proof:
that the lift respects the structure map. It reduces to the cone leg's own triangle
(`(c.π.app _).w`) after `Subtype.ext`, so it costs one `congrArg`. -/
noncomputable def fixedConeUnderIsLimit : IsLimit (fixedConeUnder k G A) where
  lift c := Under.homMk (V := fixedUnder k G A)
    (CommRingCat.ofHom (R := c.pt.right) (S := FixedPoints.subalgebra k A G)
      { toFun := fun t => ⟨(c.π.app (SingleObj.star G)).right.hom t, by
          intro g
          have h := c.w (SingleObj.toEnd G g)
          exact congrArg (fun (f : c.pt ⟶ (actionDiagramUnder k G A).obj (SingleObj.star G)) =>
            f.right.hom t) h⟩
        map_one' := by ext; exact map_one _
        map_mul' := by intro x y; ext; exact map_mul _ _ _
        map_zero' := by ext; exact map_zero _
        map_add' := by intro x y; ext; exact map_add _ _ _ })
    (by
      apply CommRingCat.hom_ext
      ext r
      refine Subtype.ext ?_
      have h : (c.π.app (SingleObj.star G)).right.hom (c.pt.hom.hom r)
          = (algebraMap k A) r :=
        (congrArg (fun (f : k ⟶ CommRingCat.of A) => f.hom r)
          (c.π.app (SingleObj.star G)).w : _)
      exact h)
  fac c j := by
    obtain rfl : j = SingleObj.star G := Subsingleton.elim _ _
    apply (Under.forget k).map_injective
    apply CommRingCat.hom_ext
    ext t
    rfl
  uniq c m hm := by
    apply (Under.forget k).map_injective
    apply CommRingCat.hom_ext
    ext t
    refine Subtype.ext ?_
    have h := hm (SingleObj.star G)
    exact congrArg (fun (f : c.pt ⟶ (actionDiagramUnder k G A).obj (SingleObj.star G)) =>
      f.right.hom t) h

/-- **The `HasLimit` form over the base.** -/
theorem hasLimit_actionDiagramUnder : HasLimit (actionDiagramUnder k G A) :=
  ⟨⟨⟨fixedConeUnder k G A, fixedConeUnderIsLimit k G A⟩⟩⟩

/-! ## §3. Dualised into `(Under k)ᵒᵖ` — the consumer's category and variance

A quotient is a colimit, and `SymPowColimit`'s affine statement lives in `(Under k)ᵒᵖ`. Both
now match: this is the same mathematics as `SymPowInvariants.fixedCoconeIsColimitOp`, in the
category that file could not reach. -/

/-- **The affine quotient over the base, as a colimit in `(Under k)ᵒᵖ`.**

Geometrically: `Spec_k (A^G)` is the quotient of `Spec_k A` by `G`, as a `k`-scheme. This is
the statement in the category and variance of
`SymPowColimit.symPowData_affineAlgebra`. -/
noncomputable def fixedCoconeUnderIsColimitOp :
    IsColimit (fixedConeUnder k G A).op :=
  (fixedConeUnderIsLimit k G A).op

/-- **The `HasColimit` form in `(Under k)ᵒᵖ`**, with the colimit a named object. -/
theorem hasColimit_actionDiagramUnder_op : HasColimit (actionDiagramUnder k G A).op :=
  ⟨⟨⟨(fixedConeUnder k G A).op, fixedCoconeUnderIsColimitOp k G A⟩⟩⟩

end UnderInvariants

/-! ## §4. The whole stack at Milne's ring

Everything above is for an arbitrary `k`-linear action. Instantiating at
`G := S_n`, `A := A^{⊗ n}` with the action of `Albanese/SymPowTensorAction.lean` gives
Milne III.3 Proposition 3.1's affine half **over the base**, with the carrier named:
`Spec_k ((A^{⊗ n})^{S_n})` is the quotient of `(Spec_k A)^n` by the permutation action.

The two hypotheses the instantiation needs — a `MulSemiringAction` and an `SMulCommClass` —
are both supplied there, not assumed: `permMulSemiringAction` and `permSMulCommClass`. As in
`SymPowTensorAction` §4, `Fin n` and `Type 0` are forced by `Under k`'s universe wanting the
group in the same universe as the ring. -/

open PiTensorProduct TensorProduct

variable (k : CommRingCat.{0}) (A : Type) [CommRing A] [Algebra k A] (n : ℕ)

/-- **Milne's affine carrier is a quotient over the base** — the whole stack at his ring.

`(A^{⊗ n})^{S_n}`, as a `k`-algebra, is the limit of the `S_n`-action on `A^{⊗ n}` in
`Under k`; dually `Spec_k` of it is the quotient of `(Spec_k A)^n`. This is the affine half of
Milne III.3 Proposition 3.1 in the category and variance
`SymPowColimit.symPowData_affineAlgebra` uses.

Still **not** `Sym^n C` for a proper curve: that is the gluing, and no glue data is built
here. See this file's scope section. -/
theorem hasColimit_actionDiagramUnder_op_symTensorPow :
    letI := permMulSemiringAction (k : Type) (ι := Fin n) A
    letI := permSMulCommClass (k : Type) (ι := Fin n) A
    HasColimit (actionDiagramUnder k (Equiv.Perm (Fin n)) (⨂[(k : Type)] _ : Fin n, A)).op :=
  letI := permMulSemiringAction (k : Type) (ι := Fin n) A
  letI := permSMulCommClass (k : Type) (ι := Fin n) A
  hasColimit_actionDiagramUnder_op _ _ _

/-- **The limit form of the same statement**: `(A^{⊗ n})^{S_n}` is the limit of the
`S_n`-action over `k`. -/
theorem hasLimit_actionDiagramUnder_symTensorPow :
    letI := permMulSemiringAction (k : Type) (ι := Fin n) A
    letI := permSMulCommClass (k : Type) (ι := Fin n) A
    HasLimit (actionDiagramUnder k (Equiv.Perm (Fin n)) (⨂[(k : Type)] _ : Fin n, A)) :=
  letI := permMulSemiringAction (k : Type) (ι := Fin n) A
  letI := permSMulCommClass (k : Type) (ι := Fin n) A
  hasLimit_actionDiagramUnder _ _ _

/-! ## §5. The index category is `(SingleObj G)ᵒᵖ`, not `SingleObj G` — and that gap is real

A trap caught while checking whether §3's colimit statement can actually be *consumed*, and
worth a lemma rather than a remark. `Functor.op` sends `F : SingleObj G ⥤ C` to
`F.op : (SingleObj G)ᵒᵖ ⥤ Cᵒᵖ`, so `hasColimit_actionDiagramUnder_op` is a statement about a
diagram indexed by **`(SingleObj G)ᵒᵖ`**. But `SymPowColimit.permDiagram` — what
`symPowData_of_hasColimit` consumes — is indexed by `SingleObj (Equiv.Perm (Fin n))` itself.
Those are different index categories, so "same category, same variance" was two thirds of the
story and the shape was the missing third.

They are *equivalent*, because a groupoid is equivalent to its opposite via `g ↦ g⁻¹`
(`Groupoid.invEquivalence`), and `hasColimit_singleObj_of_op` below transports the colimit
along it. Note what the transported diagram is: precomposition with that equivalence
reindexes the action by inversion, which is `rfl`-checked in
`invEquivalence_comp_op_map` — the *same* `σ ↦ σ⁻¹` bookkeeping that
`SymPowTensorAction.permMulSemiringAction` and `SymPowColimit.permEnd` each carry, appearing a
third time. Three independent occurrences of one inversion is a sign the convention is
coherent, not that something is off.

What this does **not** do: it does not rewrite `symPowData_affineAlgebra` to consume the named
carrier. That file's diagram is built from the `n`-fold coproduct of algebras, this one's from
the tensor power. **Superseded in part (2026-07-29):** this paragraph used to say identifying
those at `n ≥ 3` is "a missing brick rather than an alignment". The identification is now
proved (`Albanese/TensorPowerCoproduct.lean`, with both equivariance clauses); what is left is
the `Cofan`/`IsColimit` packaging in `(Under k)ᵒᵖ`, which *is* alignment. See (b) in the header.

The universe binder here is `{C : Type w} [Category.{v} C]` deliberately. With everything pinned
to `u` the lemma cannot be instantiated at `Under k` (`Category.{u, u+1}`) — it was landed that
way and was true but unusable at the only category that matters. The proof is unchanged; only
the binder moved. -/

/-- **Transport across the groupoid inverse equivalence.** A colimit of `F.op` — indexed by
`(SingleObj G)ᵒᵖ` — yields a colimit of a diagram indexed by `SingleObj G`, namely `F.op`
reindexed by inversion. This is what makes §3's statement usable by a consumer written
against `SingleObj G`. -/
theorem hasColimit_singleObj_of_op {G : Type u} [Group G] {C : Type w} [Category.{v} C]
    (F : SingleObj G ⥤ C) [HasColimit F.op] :
    HasColimit ((Groupoid.invEquivalence (SingleObj G)).functor ⋙ F.op) :=
  inferInstance

/-- **The reindexing is exactly inversion**, on the nose. So the transported diagram of
`hasColimit_singleObj_of_op` is the original action read backwards — the third appearance of
the `σ ↦ σ⁻¹` convention in this cone. -/
theorem invEquivalence_comp_op_map {G : Type u} [Group G] {C : Type w} [Category.{v} C]
    (F : SingleObj G ⥤ C) (g : G) :
    ((Groupoid.invEquivalence (SingleObj G)).functor ⋙ F.op).map (SingleObj.toEnd G g)
      = (F.map (SingleObj.toEnd G g⁻¹)).op := rfl

end AlgebraicGeometry

