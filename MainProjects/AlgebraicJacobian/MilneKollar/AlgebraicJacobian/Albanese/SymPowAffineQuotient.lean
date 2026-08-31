/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowAffineCarrier

/-!
# Milne III.3.1's affine half, with the carrier named: `Sym^n (Spec_k A) = Spec_k (A^{⊗n})^{S_n}`

This file writes the composition that `Albanese/SymPowAffineCarrier.lean`'s Scope section named
as the one thing still separating the two named ends of the affine picture, and that
`Albanese/SymPowColimit.lean` §5 flagged in bold as "**The carrier is not named in Lean.**"
With this file that caveat is discharged; §5 now records it as deleted rather than standing.

Three landed results, none of which was enough alone:

* `SymPowInvariantsUnder.hasColimit_actionDiagramUnder_op` — the quotient of the `S_n`-action
  **on the tensor power** is `op` of the invariant subalgebra. The *output*, named, but as a
  diagram indexed by `(SingleObj G)ᵒᵖ`.
* `SymPowAffineCarrier.tensorPowerOpIsoPiObj` — the `n`-fold product in `(Under k)ᵒᵖ` that
  `permDiagram` is built on **is** `op` of the tensor power, with the actions matched. The
  *input*, named.
* `SymPowInvariantsUnder.hasColimit_singleObj_of_op` — the index-category transport, along
  `Groupoid.invEquivalence`.

What this file does is note that the three compose, and that the composition is a diagram
**isomorphism** rather than a chain of rewrites: `permDiagram (op (mkUnder k A)) n` and the
transported action diagram agree at the object by `tensorPowerOpIsoPiObj` and at every map by
`permAut_eq_op_permAlgHom`, so `NatIso.ofComponents` applies and `hasColimit_of_iso` transports.

## Main results

* `transportedActionDiagram` — the action diagram on `⨂[k] _ : Fin n, A`, transported to the
  index category `SingleObj (Equiv.Perm (Fin n))` that `permDiagram` uses.
* `transportedActionDiagram_map` — its map at `σ` is `op (permAlgHom σ)`, on the nose after one
  `Under.forget`/`CommRingCat.hom_ext` peel. Note the variance: **no inverse here**, because the
  two inversions in the chain (`permMulSemiringAction` acts through `σ⁻¹`, and the
  `invEquivalence` reindexes by `σ ↦ σ⁻¹`) cancel.
* `permDiagramIsoTransportedAction` — **the diagram isomorphism**, the content of this file.
* `hasColimit_permDiagram_op_mkUnder` — a stepping stone, **not** a new fact: cocompleteness
  already gives this instance (`infer_instance` discharges it). Its value is that its proof
  factors through the named vertex.
* `colimitPermDiagramIsoFixed` — **the deliverable.** The colimit of the `S_n`-action on
  `(Spec_k A)^n` **is** `Spec_k ((A^{⊗ n})^{S_n})`. An equation between the anonymous colimit and
  a named object, so — unlike the `HasColimit` above — it is not obtainable from cocompleteness.

An earlier draft offered instead a restatement of `symPowData_affineAlgebra` "reached through"
the new instance. That was vacuous: the statement is literally the old one, and which proof
supplied the instance is invisible in it. Naming an object requires a statement that mentions the
object.

## The variance ledger, because this cone has got it wrong twice

Four inversions appear along this chain and they must be counted, not guessed:

1. `permEnd C n σ = permAut C σ⁻¹` (the `End`-multiplication convention);
2. `permMulSemiringAction` acts by `σ • x = permAlgHom σ⁻¹ x`;
3. `invEquivalence` reindexes the transported diagram by `σ ↦ σ⁻¹`;
4. `inj i ≫ permAlgHom e = inj (e⁻¹ i)`, which forces `permAut_eq_op_permAlgHom` to pair
   `permAut e` with `permAlgHom e⁻¹`.

(2) and (3) cancel, leaving `transportedActionDiagram_map` inverse-free; (1) and (4) cancel in
the naturality square, which is why it closes by `permAut_eq_op_permAlgHom` after one `inv_inv`
and no further bookkeeping. The `e⁻¹` in (4) was got backwards on the first attempt in the
sibling file and caught by a residual goal true only at an involution.

**Both cancellations are machine-checked, not read off the list.** Each of (1)–(4) was
re-derived as a standalone example, and so was the composite endpoint: at
`permDiagram.map σ = permAut σ⁻¹` the algebra side is `permAlgHom (σ⁻¹)⁻¹ = permAlgHom σ`, which
is exactly what (2)+(3) deliver — so the square closes and nothing is left over. A ledger of
inversions is the kind of claim that stays self-consistent while being wrong (this project
records a case where a degree ledger faithfully recomputed an inverted twist), so counting them
is not evidence; deriving the endpoint is.

## Scope — the curve is untouched

**Does**: name the affine carrier. `SymPowColimit.lean` §5's bold caveat is now dischargeable,
and the honest statement of Milne III.3 Proposition 3.1's affine half — the object, not merely
its existence — is `colimitPermDiagramIsoFixed` together with
`SymPowInvariantsUnder.fixedUnder`.

**Does not**: touch the gluing. `HasColimit (permDiagram C n)` for a proper curve `C` in
`Over (Spec k̄)` is a statement about a non-affine object, and nothing here bears on it —
`AlbaneseUP.lean`'s six sorries are unchanged and `albanese_universal_property` still reports
`sorryAx`. Milne's route from here is to glue these affine quotients over an open affine cover
of the curve (`SymPowColimit.lean` §6's availability table), which needs their compatibility on
overlaps and is the remaining item of `StableAffineCoverGroup.lean`'s four-item bill.

**And one gap that is easy to overlook, because a name exists for it.** The capstone
`AlbaneseFromColimit.exists_unique_albanese_of_scheme_colimits` binds
`HasColimit (permDiagram C g)` for `C : Over (Spec (.of k̄))` — a diagram in **`Over (Spec k̄)`,
a category of schemes**. Everything here is a diagram in **`(Under k)ᵒᵖ`, a category of
algebras**. `CategoryTheory.Over.opEquivOpUnder` does exist, and it is tempting to read it as
the bridge, but its statement is `Over (op X) ≌ (Under X)ᵒᵖ` **inside one category** — at
`X := k` that is a statement about `CommRingCat`, not about `Scheme`. Crossing to
`Over (Spec k̄)` additionally needs `AffineScheme.equivCommRingCat` and the identification of
`(Under k)ᵒᵖ` with affine `k`-schemes, which `SymPowColimit.lean` §5 lists as its *first*
unbuilt bridge and which nothing in this cone supplies. So the affine chain cannot feed the
capstone today even for an affine curve — a second gap beside the gluing, and the one whose
absence is disguised by a plausibly-named mathlib lemma.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry

namespace PiTensorProduct

section AffineQuotient

variable (k : CommRingCat.{0}) (A : Type) [CommRing A] [Algebra k A] (n : ℕ)

/-- The cartesian structure on `(Under k)ᵒᵖ`, spelled the way `symPowData_affineAlgebra` spells
it — `ofHasFiniteProducts`, not a bound `[CartesianMonoidalCategory _]` hypothesis.

**This is load-bearing and not stylistic.** With the instance *bound*, `permDiagram`'s object
`∏ᶜ` and `tensorPowerOpIsoPiObj`'s codomain are `rfl`-equal but not syntactically equal, and the
naturality `rw` fails with "not type-correct under the `instances` transparency level" — the
project's recorded `rfl`-equal-spellings trap. Pinning the concrete instance makes both sides one
term. It also matches the consumer, which is the reason to prefer it anyway. -/
noncomputable local instance instCartesianUnderOp :
    CartesianMonoidalCategory (Under k)ᵒᵖ := ofHasFiniteProducts

/-! ## §1. The action diagram, on the index category `permDiagram` uses

`hasColimit_actionDiagramUnder_op` is about a diagram over `(SingleObj G)ᵒᵖ`. Precomposing with
`Groupoid.invEquivalence` lands it over `SingleObj G`, which is `permDiagram`'s index category.
The reindexing is `σ ↦ σ⁻¹` — see the variance ledger in the module header for why the result is
nevertheless inverse-free. -/

/-- **The transported action diagram.** The `S_n`-action on `⨂[k] _ : Fin n, A` over the base,
dualised into `(Under k)ᵒᵖ` and reindexed onto `SingleObj (Equiv.Perm (Fin n))`. -/
noncomputable def transportedActionDiagram :
    SingleObj (Equiv.Perm (Fin n)) ⥤ (Under k)ᵒᵖ :=
  letI := permMulSemiringAction (k : Type) (ι := Fin n) A
  letI := permSMulCommClass (k : Type) (ι := Fin n) A
  (Groupoid.invEquivalence (SingleObj (Equiv.Perm (Fin n)))).functor
    ⋙ (actionDiagramUnder k (Equiv.Perm (Fin n)) (⨂[(k : Type)] _ : Fin n, A)).op

/-- **The transported diagram's map is `op (permAlgHom σ)`, with no inverse.**

The two inversions in the chain cancel: `permMulSemiringAction` acts through `σ⁻¹`, and
`invEquivalence` reindexes by `σ ↦ σ⁻¹`. The proof peels `Under.forget` and `CommRingCat.hom_ext`
and is then `rfl` — the cancellation is definitional, not a rewrite. -/
theorem transportedActionDiagram_map (σ : Equiv.Perm (Fin n)) :
    (transportedActionDiagram k A n).map (SingleObj.toEnd (Equiv.Perm (Fin n)) σ)
      = ((permAlgHom (k : Type) A σ).toUnder).op := by
  apply Quiver.Hom.unop_inj
  apply (Under.forget k).map_injective
  apply CommRingCat.hom_ext
  ext x
  rfl

/-! ## §2. The diagram isomorphism

Object: `tensorPowerOpIsoPiObj`. Maps: `permAut_eq_op_permAlgHom`. That is the whole content —
which is the point, since the two halves were landed separately and never compared. -/

/-- **The comparison of diagrams.** `permDiagram (op (mkUnder k A)) n` — the diagram whose
colimit `symPowData_affineAlgebra` takes — is isomorphic to the transported action diagram on the
tensor power.

Naturality is `permAut_eq_op_permAlgHom` after `inv_inv`: `permDiagram`'s map at `σ` is
`permAut σ⁻¹` by the `permEnd` convention, and that pairs with `permAlgHom σ`. -/
noncomputable def permDiagramIsoTransportedAction :
    transportedActionDiagram k A n
      ≅ permDiagram (Opposite.op (CommRingCat.mkUnder k A)) n :=
  NatIso.ofComponents (fun _ => tensorPowerOpIsoPiObj k A n) (by
    intro X Y f
    obtain rfl : X = SingleObj.star _ := Subsingleton.elim _ _
    obtain rfl : Y = SingleObj.star _ := Subsingleton.elim _ _
    -- State each side with `.map f` and let unification supply the `toEnd`: writing
    -- `toEnd _ f` in the rewrite makes the pattern syntactically distinct from the goal
    -- (see the `instCartesianUnderOp` docstring — the same spelling trap, one layer up).
    have h1 : (transportedActionDiagram k A n).map f
        = ((permAlgHom (k : Type) A (f : Equiv.Perm (Fin n))).toUnder).op :=
      transportedActionDiagram_map k A n _
    have h2 : (permDiagram (Opposite.op (CommRingCat.mkUnder k A)) n).map f
        = MonObj.permAut (Opposite.op (CommRingCat.mkUnder k A))
            (f : Equiv.Perm (Fin n))⁻¹ := rfl
    rw [h1, h2]
    have h := permAut_eq_op_permAlgHom k A n (f : Equiv.Perm (Fin n))⁻¹
    rw [inv_inv] at h
    exact h.symm)

/-! ## §3. The payoff: the colimit comes from the invariants

`symPowData_affineAlgebra` obtains its colimit from `(Under k)ᵒᵖ`'s cocompleteness, so its
carrier is an anonymous `colimit` and Milne's `(A^{⊗n})^{S_n}` appears nowhere. **The fix is not
a second proof of the same `HasColimit`** — that changes nothing provable, as the next docstring
records — but an *equation* between the colimit object and the named one, which is
`colimitPermDiagramIsoFixed` at the end of this section. The `HasColimit` below is a stepping
stone to it, not the deliverable. -/

/-- **`HasColimit` for the affine chart, proved through the named vertex.**

`(Under k)ᵒᵖ` is cocomplete, so this instance is available without this file — `infer_instance`
discharges it, measured — and **this theorem is therefore not a new fact and not the point.** Its
only role is that its proof factors through `permDiagramIsoTransportedAction`, which is what
`colimitPermDiagramIsoFixed` then needs. Do not cite it as progress on naming the carrier; cite
the iso. -/
theorem hasColimit_permDiagram_op_mkUnder :
    HasColimit (permDiagram (Opposite.op (CommRingCat.mkUnder k A)) n) := by
  letI := permMulSemiringAction (k : Type) (ι := Fin n) A
  letI := permSMulCommClass (k : Type) (ι := Fin n) A
  haveI : HasColimit (transportedActionDiagram k A n) := by
    haveI := hasColimit_actionDiagramUnder_op k (Equiv.Perm (Fin n))
      (⨂[(k : Type)] _ : Fin n, A)
    infer_instance
  exact hasColimit_of_iso (permDiagramIsoTransportedAction k A n).symm

/-! ### The statement that actually names the carrier

**A probe, and a correction to what this file first claimed.** A draft of this file offered
`symPowData_affine_named : ∃ D, ∀ σ, permAut ≫ D.proj = D.proj` as its payoff, on the grounds
that it was "reached through `hasColimit_permDiagram_op_mkUnder`". That was worthless: the
statement is *identical* to `symPowData_affineAlgebra` instantiated at `op (mkUnder k A)`, and
which proof produces the instance is invisible in it. Worse, `infer_instance` discharges
`HasColimit (permDiagram (op (mkUnder k A)) n)` on its own from cocompleteness — measured — so
even `hasColimit_permDiagram_op_mkUnder` adds nothing to what is *provable*; its only value is
that its proof factors through the named vertex.

Naming the carrier therefore has to be an **equation about the colimit object**, which is the
theorem below. That is the one statement in this cone that mentions Milne's `(A^{⊗ n})^{S_n}` and
the diagram whose colimit `symPowData_affineAlgebra` takes, in the same sentence. -/

/-- **Milne III.3 Proposition 3.1, affine half, with the object identified.**

The colimit of the `S_n`-action on `(Spec_k A)^n` — the very diagram
`SymPowColimit.symPowData_affineAlgebra` takes a colimit of — is `Spec_k` of the invariant
subalgebra `(A^{⊗ n})^{S_n}`.

This is what `SymPowColimit.lean` §5's former bold caveat "**The carrier is not named in Lean**"
asked for, and unlike the `HasColimit` statement above it is not obtainable from
cocompleteness: it is an equation between the anonymous colimit and a named object, needing both
`permDiagramIsoTransportedAction` (this file) and `fixedCoconeUnderIsColimitOp`
(`SymPowInvariantsUnder`).

Two colimits of isomorphic diagrams, composed with `whiskerEquivalence` to absorb the
index-category transport.

**Checked that this is not free, after the `hasColimit` lesson above.** Generic uniqueness of
colimits relates two colimits *of the same diagram*, and the invariants cocone is a cocone on
`transportedActionDiagram`, not on `permDiagram` — so the argument would collapse only if those
two diagrams were definitionally equal. They are **not**: `rfl` between them fails
("`transportedActionDiagram k A n` is not definitionally equal to
`permDiagram (op (mkUnder k A)) n`"), measured. So `permDiagramIsoTransportedAction` is
load-bearing, and unlike `hasColimit_permDiagram_op_mkUnder` this theorem is not reachable
without the two object comparisons it composes.

**Two non-vacuity checks, since an identification can be true and say nothing.** Both measured:

* the right-hand object really is Milne's. `(fixedUnder k (Perm (Fin n)) (⨂[k] _ : Fin n, A))`
  is `FixedPoints.subalgebra k (⨂[k] _ : Fin n, A) (Perm (Fin n))` by `rfl` — the invariant
  subalgebra, not some other object that happens to sit at that index;
* the action being quotiented by is not trivial. `permAlgHom k A (Equiv.swap 0 1)` is **not**
  definitionally `AlgHom.id` at `n = 2`, so the `S_n`-quotient is a genuine quotient. Had it
  been the identity, the "quotient" would be the tensor power itself and the theorem would be
  an elaborate `Iso.refl`. This is the same trivial-witness discipline `SymPowInterface.lean`
  applies to `symPowDataTrivial`. -/
noncomputable def colimitPermDiagramIsoFixed :
    letI := permMulSemiringAction (k : Type) (ι := Fin n) A
    letI := permSMulCommClass (k : Type) (ι := Fin n) A
    haveI := hasColimit_permDiagram_op_mkUnder k A n
    colimit (permDiagram (Opposite.op (CommRingCat.mkUnder k A)) n)
      ≅ Opposite.op (fixedUnder k (Equiv.Perm (Fin n)) (⨂[(k : Type)] _ : Fin n, A)) := by
  letI := permMulSemiringAction (k : Type) (ι := Fin n) A
  letI := permSMulCommClass (k : Type) (ι := Fin n) A
  haveI := hasColimit_permDiagram_op_mkUnder k A n
  refine (HasColimit.isoOfNatIso (permDiagramIsoTransportedAction k A n).symm) ≪≫ ?_
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (IsColimit.whiskerEquivalenceEquiv _ (fixedCoconeUnderIsColimitOp k (Equiv.Perm (Fin n))
      (⨂[(k : Type)] _ : Fin n, A)))

end AffineQuotient

end PiTensorProduct
