/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowColimit

/-!
# Naming the affine symmetric-power carrier: the quotient is `Spec` of the invariants

`Albanese/SymPowColimit.lean` reduced the symmetric-power obligation to one instance,
`HasColimit (permDiagram C n)`, and proved that the affine-algebra case is *inhabited*
at every `n`. But it flagged, three times and deliberately, that the resulting object
was **not identified**:

> `mem_sections_singleObj_iff` is the *reason to expect* it … but it is a statement about
> `SingleObj G ⥤ Type` and mentions neither `CommRingCat` nor `Spec`. **The carrier is not
> named in Lean.**

The *naming* half of that gap is answered here: the colimit of a group action on a ring,
taken in `CommRingCatᵒᵖ`, is `A^G`. It becomes Milne's `(A^{⊗n})^{S_n}` only once `A` is
the `n`-fold tensor power carrying the `S_n`-action — which is **not** supplied below (see
the scope section). So read this as *the carrier of a ring-action quotient is now a named
object with a proved universal property*, not as *`SymPowColimit`'s flagged obligation is
discharged by this file*.

**Update 2026-07-29 (run 0069 r7): the three things this file left open have all landed, and
the quoted caveat is deleted.** The paragraph above used to end "that obligation also wants the
tensor power, the `S_n`-action on it, and a category match, and all three are still open".
Each is now supplied: the action is `SymPowTensorAction.permMulSemiringAction`, the category
match is `SymPowInvariantsUnder.fixedCoconeUnderIsColimitOp`, and the composition identifying
the colimit is `SymPowAffineQuotient.colimitPermDiagramIsoFixed`. `SymPowColimit.lean` §5 no
longer carries the bold caveat quoted above; do not cite it as live.

## Why naming the carrier is real content, not bookkeeping

The inhabitation statement `symPowData_affineAlgebra` comes from mathlib's colimits and
says only *some* object has the universal property. Milne III.3 Proposition 3.1 says what
it **is**, and the difference is not cosmetic: the gluing step — the leg's remaining work
— has to compare the quotients of two overlapping charts. A comparison needs a formula for
each side. An abstract `colimit (permDiagram …)` supports no such comparison; `A^G` does,
because restriction of invariants along `A → A_b` is a ring map one can write down.

So this file supplies a prerequisite for gluing rather than restating what was known. The
"no consumer" note that stood here is now **false and retracted**: it read "no declaration in
the tree consumes it yet (grep for `fixedConeIsLimit` outside this file returns nothing)".
As of run 0069 r7 `fixedConeIsLimit` is consumed by
`Albanese/SymPowInvariantsUnder.lean` (the `Under k` insertion) and
`Albanese/SymPowTensorAction.lean` (at the tensor-power action), and downstream of those by
`Albanese/SymPowAffineQuotient.lean`. Still modest, and for a different reason: the chain is
`k`-algebra language over `mkUnder k A`, whereas the gluing is about a proper curve.

## Main results

* `actionDiagram G A` — the one-object diagram in `CommRingCat` of a `MulSemiringAction`.
  This is `permDiagram`'s algebraic counterpart: same index category `SingleObj G`.
* `fixedCone` / `fixedConeIsLimit` — **the identification, as a limit in `CommRingCat`**:
  the cone over `actionDiagram` with vertex the fixed subring `A^G` (mathlib's
  `FixedPoints.subring`) is a limit cone. Nothing is assumed about `G` — not even
  finiteness — because the universal property of the invariants needs none.
* `fixedCoconeIsColimitOp` — the same fact **dualised**: in `CommRingCatᵒᵖ`, `A^G` is a
  *colimit* of the action, which is the variance a quotient has.
* `hasColimit_actionDiagram_op` — hence the `HasColimit` statement for the opposite
  diagram, with the carrier now named.

**One category caveat, and it is load-bearing — a fresh-context review caught an earlier
draft of this header asserting otherwise.** `SymPowColimit`'s affine statement
(`symPowData_affineAlgebra`) lives in `(Under k)ᵒᵖ`, the opposite of `k`-algebras; this file
lives in `CommRingCatᵒᵖ`, with no base ring. **Those are different categories**, and no
declaration here bridges them (`Over.opEquivOpUnder` and `AffineScheme.equivCommRingCat`
exist in mathlib but are not used below). So nothing in `SymPowColimit.lean` can currently
*consume* `hasColimit_actionDiagram_op`: this is a parallel identification of the same
mathematics over a different base, not a plugged-in input.

**Which of the two exits was taken (2026-07-29, run 0069 r7).** This paragraph used to end
"Supplying the bridge — or restating the below over `Under k` — is unfinished work", offering two
routes. The **second** was taken: `Albanese/SymPowInvariantsUnder.lean` rebuilds the cone
directly in `Under k` (the invariant subalgebra already *is* a `k`-algebra, so no transport is
needed), and `Albanese/SymPowAffineQuotient.lean` then identifies the colimit. So that clause is
no longer outstanding work — but note what did **not** happen: the *bridge* was never built, and
`Over.opEquivOpUnder` is still unused here. Anyone wanting `CommRingCatᵒᵖ`-side results in
`(Under k)ᵒᵖ` should restate as that file does, not look for a transport.

The genuinely unfinished crossing is a different one: from `(Under k)ᵒᵖ` to *affine `k`-schemes*
(`AffineScheme.equivCommRingCat`), which is what would turn all of this from `k`-algebra language
into `Spec`-language. `Over.opEquivOpUnder` does not do it — its statement stays inside one
category, so at `X := k` it is about `CommRingCat`, not `Scheme`.

## Scope — read this before quoting it

What is proved is the **affine, algebraic** identification: a limit in `CommRingCat` and
its dual in `CommRingCatᵒᵖ`. Two things are deliberately *not* claimed:

* This is not `Sym^n C` for a proper curve. The curve case is the gluing, and the gluing
  is not here. `SymPowColimit`'s §6 boundary sentence still stands verbatim: the affine
  universal property transfers into `Scheme` only against *affine* test objects.
* The index category here is `SingleObj G` for an arbitrary group acting on an arbitrary
  ring. Specialising `G := Equiv.Perm (Fin n)` and `A := A^{⊗ n}` is what makes it Milne's
  statement; that specialisation needs the `S_n`-action on the tensor power, which mathlib
  has only for modules and which is **not built here** — it is built in
  `Albanese/SymPowTensorAction.lean` (`permMulSemiringAction`), and the specialisation is
  carried out in `Albanese/SymPowAffineQuotient.lean` (`colimitPermDiagramIsoFixed`), both
  run 0069 r7. So this bullet bounds *this file*, not the tree.

So: the carrier of the affine quotient is now a named object with a written-down universal
property, which is what the next step consumes. It is not the symmetric power of a curve.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94. The consumer is
`Albanese/SymPowColimit.lean` §5; the interface is `Albanese/SymPowInterface.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## §1. The action as a diagram in `CommRingCat`

`permDiagram` (`Albanese/SymPowColimit.lean`) bundles a group action as a functor out of
`SingleObj G`. The algebraic counterpart is the same construction with `End` taken in
`CommRingCat`, and the convention point is the mirror image of the one recorded there:
here the action is *covariant* on the ring, so no inverse is needed — a ring-level
`MulSemiringAction` composed with mathlib's `End` multiplication comes out right on the
nose (`mul_smul`). Contrast `permEnd`, which needs `σ⁻¹` because it acts on the
*geometric* side. -/

/-- **A ring action, as a one-object diagram in `CommRingCat`.**

The single value is `A` and the endomorphism at `g` is the ring automorphism `x ↦ g • x`.
A *limit* of this diagram is the invariant subring; dually, a colimit in `CommRingCatᵒᵖ`
is the affine quotient. -/
noncomputable def actionDiagram (G : Type u) [Group G] (A : Type u) [CommRing A]
    [MulSemiringAction G A] : SingleObj G ⥤ CommRingCat.{u} :=
  SingleObj.functor (M := G) (X := CommRingCat.of A)
    { toFun := fun g => CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)
      map_one' := by apply CommRingCat.hom_ext; ext x; simp
      map_mul' := by
        intro g h
        apply CommRingCat.hom_ext
        ext x
        change (g * h) • x = g • h • x
        rw [mul_smul] }

variable (G : Type u) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]

@[simp]
theorem actionDiagram_obj (j : SingleObj G) :
    (actionDiagram G A).obj j = CommRingCat.of A := rfl

/-- The diagram's map at `g` is the action of `g`, on elements. -/
theorem actionDiagram_map_apply (g : G) (x : A) :
    ((actionDiagram G A).map (SingleObj.toEnd G g)).hom x = g • x := rfl

/-! ## §2. The invariants are the limit

This is the identification. The cone is the inclusion `A^G ↪ A`, whose cone condition is
exactly "an invariant element is fixed by every `g`"; the limit property is the universal
property of a subtype — a cone vertex maps into `A` landing in the invariants, because the
cone condition *says* its image is fixed.

Note what is **not** assumed: `G` is not finite, `A` is not Noetherian, and no integrality
enters. Finiteness is needed for the *geometry* of the quotient map (integrality,
surjectivity of `Spec A → Spec A^G`); the universal property itself is free. -/

/-- **The cone over the action with vertex the invariant subring.** Its cone condition is
`x = g • x` for `x ∈ A^G`, i.e. the defining property of `FixedPoints.subring`. -/
noncomputable def fixedCone : Cone (actionDiagram G A) where
  pt := CommRingCat.of (FixedPoints.subring A G)
  π :=
    { app := fun _ => CommRingCat.ofHom (FixedPoints.subring A G).subtype
      naturality := by
        intro X Y f
        apply CommRingCat.hom_ext
        ext (x : FixedPoints.subring A G)
        change ((x : A)) = (f : G) • (x : A)
        exact (x.2 _).symm }

@[simp]
theorem fixedCone_pt :
    (fixedCone G A).pt = CommRingCat.of (FixedPoints.subring A G) := rfl

/-- **Milne's `(A^{⊗n})^{S_n}`, in the general form: the invariants ARE the limit.**

The cone of `fixedCone` is a limit cone. Given any cone `c`, its leg at the unique object
lands in the invariants precisely by the cone condition `c.w`, so the lift is that leg
corestricted to `A^G`; uniqueness is injectivity of the inclusion.

This is the declaration that names the carrier. `SymPowColimit`'s
`mem_sections_singleObj_iff` said a one-object diagram's *sections* are its fixed points,
about `SingleObj G ⥤ Type`; this says the *limit in `CommRingCat`* is the fixed
**subring**, which is the statement the quotient construction needs. -/
noncomputable def fixedConeIsLimit : IsLimit (fixedCone G A) where
  lift c := CommRingCat.ofHom
    { toFun := fun t => ⟨(c.π.app (SingleObj.star G)).hom t, by
        intro g
        have h := c.w (SingleObj.toEnd G g)
        exact congrArg (fun (f : c.pt ⟶ CommRingCat.of A) => f.hom t) h⟩
      map_one' := by ext; exact map_one _
      map_mul' := by intro x y; ext; exact map_mul _ _ _
      map_zero' := by ext; exact map_zero _
      map_add' := by intro x y; ext; exact map_add _ _ _ }
  fac c j := by
    obtain rfl : j = SingleObj.star G := Subsingleton.elim _ _
    apply CommRingCat.hom_ext
    ext t
    rfl
  uniq c m hm := by
    apply CommRingCat.hom_ext
    ext t
    refine Subtype.ext ?_
    have h := hm (SingleObj.star G)
    exact congrArg (fun (f : c.pt ⟶ CommRingCat.of A) => f.hom t) h

/-- **The invariant subring, as a limit — the `HasLimit` form.** -/
theorem hasLimit_actionDiagram : HasLimit (actionDiagram G A) :=
  ⟨⟨⟨fixedCone G A, fixedConeIsLimit G A⟩⟩⟩

/-! ## §3. Dualised: the affine quotient is a colimit in `CommRingCatᵒᵖ`

A quotient is a *colimit*, so the geometric side wants the dual statement. `IsLimit.op`
crosses that gap with no further mathematics: a limit cone in `CommRingCat` is a colimit
cocone in `CommRingCatᵒᵖ` over the opposite diagram.

**Do not read this as `SymPowColimit`'s §5 obligation discharged**, which an earlier draft
of this header did. That obligation is about `(Under k)ᵒᵖ` — `k`-algebras — and the
statements below are about `CommRingCatᵒᵖ`, with no base ring. Different categories, no
bridge built here, so `symPowData_affineAlgebra` cannot consume these. What the two say
*jointly*, with that caveat live, is: the affine quotient's carrier is the invariants over
`CommRingCat`, and the interface is inhabited over `Under k`. Making those one statement is
open work. -/

/-- **The affine quotient, named, as a colimit in `CommRingCatᵒᵖ`.**

Dual to `fixedConeIsLimit`. The cocone vertex is `A^G` viewed in the opposite category —
geometrically, `Spec (A^G)` — and it is a colimit of the opposite action diagram.

This identifies the object of a ring-action quotient: dually, the quotient of `Spec A` by
`G` is `Spec (A^G)`. It is **not** Milne III.3 Proposition 3.1's affine half, which is about
the `n`-fold tensor power with its `S_n`-action; see the scope section for the two things
that specialisation still needs. Gluing such charts is a separate matter again
(`Albanese/SymPowColimit.lean` §6). -/
noncomputable def fixedCoconeIsColimitOp :
    IsColimit (fixedCone G A).op :=
  (fixedConeIsLimit G A).op

/-- **The `HasColimit` form of the affine quotient**, on the opposite of `CommRingCat`,
with the colimit a named object rather than an abstract one.

This is the same *shape* as the obligation `SymPowColimit.lean` isolates, over a different
category (`CommRingCatᵒᵖ`, not `(Under k)ᵒᵖ` and not `Over (Spec k̄)`), so it does not
discharge it. -/
theorem hasColimit_actionDiagram_op : HasColimit (actionDiagram G A).op :=
  ⟨⟨⟨(fixedCone G A).op, fixedCoconeIsColimitOp G A⟩⟩⟩

/-! ## §4. What this does and does not settle

**Settled.** The carrier of a quotient by a ring action has a name and a proved universal
property, in both variances: `A^G`, with no finiteness and no Noetherian hypothesis.

**Not settled — three things, and a fresh-context review had to point out the third.**

* The curve case. `Over (Spec k̄)` with `C` proper still has no
  `HasColimit (permDiagram C g)`, and this file does not touch it.
* The specialisation to Milne's actual ring. `G := Equiv.Perm (Fin n)` acting on the
  `n`-fold tensor power `A^{⊗ n}` is the case Milne uses; the `S_n`-action on a tensor
  power of a commutative *ring* is not built here (mathlib's `SymmetricPower` /
  `TensorPower` symmetric API is for modules — `PiTensorProduct.reindex` is a *linear*
  equiv). So `A^G` above is Milne's `(A^{⊗n})^{S_n}` only once that action is supplied.
  **Supplied since run 0069 r7**, in `Albanese/SymPowTensorAction.lean`
  (`permMulSemiringAction`); this bullet now bounds only this file.
* **The category.** `SymPowColimit`'s affine statement is over `(Under k)ᵒᵖ`; everything
  here is over `CommRingCatᵒᵖ`. **Bridged since run 0069 r7** — this bullet used to end
  "No declaration bridges them, so nothing in that file can consume anything in this one",
  and that is now false: `Albanese/SymPowInvariantsUnder.lean` redoes the identification in
  `Under k` (`fixedUnder`, `fixedCoconeUnderIsColimitOp`) reusing `fixedConeIsLimit`, and
  `Albanese/SymPowAffineQuotient.lean` consumes it to identify
  `colimit (permDiagram (op (mkUnder k A)) n)`. Note *how* it was bridged: by rebuilding in
  `Under k`, **not** via `Over.opEquivOpUnder` / `AffineScheme.equivCommRingCat` as this
  bullet predicted. That `Spec`-language bridge is still unbuilt, so the whole chain remains
  `k`-algebra language.

The first two were named in the first draft of this file; the third was not, and its absence
made the header read as though the flagged obligation had been discharged. Recorded because
the pattern is this lane's recurring one (inbox `I-0571`, `I-0592`, `I-0637`): a scope
section can be scrupulous about the axis you thought of and silent about the one you did
not. What is proved is the *general* invariants identification — strictly more than the
previous inhabitation statement, strictly less than Milne III.3.1's affine case. -/

end AlgebraicGeometry
