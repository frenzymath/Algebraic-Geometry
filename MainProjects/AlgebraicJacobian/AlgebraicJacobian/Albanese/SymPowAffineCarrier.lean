/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.TensorPowerCofan
import AlgebraicJacobian.Albanese.SymPowColimit
import AlgebraicJacobian.Albanese.SymPowInvariantsUnder

/-!
# Naming the affine carrier: the `n`-fold product in `(Under k)ᵒᵖ` **is** the tensor power

`Albanese/SymPowColimit.lean` §5 states its affine result and then flags, in bold, that
`symPowData_affineAlgebra` obtains its colimit from `(Under k)ᵒᵖ`'s completeness with no
construction written — so **neither** end of Milne's affine picture is a named object there:
not the quotient `Spec_k (A^{⊗n})^{S_n}`, and not even the `(Spec_k A)^n` it is a quotient *of*,
which enters only as `∏ᶜ` in `(Under k)ᵒᵖ`.

**This file names the second one — the input, not the quotient.** Read the Scope section before
citing it for the first; conflating them is a mistake the first draft of this header made.

This file supplies the missing comparison. It is not the invariants theorem (that is
`SymPowInvariantsUnder.fixedConeUnderIsLimit`, landed) and not the coproduct universal
property (that is `TensorPowerCofan.tensorPowerCofanIsColimit`, landed last). It is the step
between them that nothing had written: **the `n`-fold product of `op (mkUnder k A)` in
`(Under k)ᵒᵖ` — the object `permDiagram` is built on — is `op (mkUnder k (⨂[k] _ : Fin n, A))`,
compatibly with the `S_n`-actions.**

## Why this was the blocking step, and why it looked like something else

`SymPowInvariantsUnder`'s header lists the obstruction as (b) *the object*:

> `symPowData_affineAlgebra` builds `permDiagram X n` from the `n`-fold *product of `X` in
> `(Under k)ᵒᵖ`* … Everything here is about `⨂[k] _ : Fin n, A`.

and prices it as needing (i) the `n`-ary coproduct comparison and (ii) the action match. Both
of those are now proved — but having them is not the same as having *this*, because
`permDiagram` is built on `∏ᶜ` in `(Under k)ᵒᵖ`, which is a `Pi.π`-shaped object, whereas the
coproduct comparison speaks about `singleAlgHom`-shaped coprojections. The bridge is one
`conePointUniqueUpToIso` against `productIsProduct`, plus the transport law
`conePointUniqueUpToIso_hom_comp` to move `Pi.π` to `op (inj i)`.

## Main results

* `tensorPowerOpIsoPiObj` — **the comparison**: `op (mkUnder k (⨂[k] _ : Fin n, A))` is the
  `n`-fold product of `op (mkUnder k A)` in `(Under k)ᵒᵖ`.
* `tensorPowerOpIsoPiObj_hom_π` — its transport law: the comparison carries `Pi.π i` to
  `op (singleAlgHom i)`. This is what makes the iso usable rather than merely true; without
  it one has an isomorphism of objects and no way to compute with it.
* `permAut_eq_op_permAlgHom` — **the action match, at the product**: the factor-permuting
  automorphism `permAut` of the categorical product corresponds, across the comparison, to
  `op (permAlgHom e)` on the tensor power. Proved by `Pi.hom_ext` from the transport law and
  `tensorPowerCofan_inj_permAlgHom`.

## The `rfl`-equal-spellings trap, recorded because it cost the first attempt

Stating the opped equivariance as a `rw` target fails with

> Did not find an occurrence of the pattern … The target expression is not type-correct under
> the `instances` transparency level

because `((f ≫ g)).op` produces `Quiver.opposite` where the goal carries
`CategoryStruct.opposite.toQuiver`. The two are `rfl`-equal and not syntactically equal, so
`rw [← op_comp]` cannot fire. `congrArg Quiver.Hom.op` applied to the un-opped lemma goes
straight through. Do not hunt for a missing `op_comp` variant; normalise the spelling instead.

## Scope — stated carefully, because this cone has over-claimed before

**Does**: name the object. After this file the affine chart of Milne III.3 Proposition 3.1 is
a *named* `k`-algebra — `⨂[k] _ : Fin n, A`, and via `SymPowInvariantsUnder` its `S_n`-fixed
subalgebra — sitting at the object `permDiagram` is built on, with the actions matched.

**Does not**:

* discharge `HasColimit (permDiagram (op (mkUnder k A)) n)` from the invariants theorem. That
  still needs the index-category transport of `SymPowInvariantsUnder` §5
  (`(SingleObj G)ᵒᵖ` versus `SingleObj G`) composed with this object comparison, and the two
  have not been composed. `symPowData_affineAlgebra` continues to obtain its colimit from
  `(Under k)ᵒᵖ`'s completeness, not from the named carrier.
* touch the curve. `HasColimit (permDiagram C n)` for a proper curve is the gluing and is
  untouched; `AlbaneseUP.lean`'s six sorries are unchanged and
  `albanese_universal_property` still reports `sorryAx`.

**A distinction to keep, because the first draft of this header collapsed it.** That draft said
`SymPowColimit.lean` §5's former bold caveat "**The carrier is not named in Lean**" was "now
false" on the strength of this file alone. It was not: that caveat was about the **colimit**
carrier — Milne's quotient `Spec_k (A^{⊗n})^{S_n}` — whereas what this file names is the
**object the action acts on**, `(Spec_k A)^n = Spec_k (A^{⊗n})`. Input, not output. Naming the
input is what was *missing*; it is not the same as naming the quotient. Keep the distinction
even now that both halves are closed, because it is what makes this file's contribution legible.

What the two compose to:

* `SymPowInvariantsUnder.hasColimit_actionDiagramUnder_op` gives the quotient of the
  `S_n`-action **on the tensor power** as `op` of the invariant subalgebra — the output, named;
* this file gives the object `permDiagram` acts on as `op` of the tensor power, with the actions
  matched — the input, named;
* the composition — the index-category transport of `SymPowInvariantsUnder` §5
  (`(SingleObj G)ᵒᵖ` versus `SingleObj G`, via `Groupoid.invEquivalence`) applied across this
  comparison — **is now written**: `SymPowAffineQuotient.colimitPermDiagramIsoFixed`
  (run 0069 r7). Until that round this bullet read "what is **not** written is the composition".

So the delta this file contributes is its *object half*; the quotient half is
`Albanese/SymPowAffineQuotient.lean`, and with it `SymPowColimit.lean` §5's bold caveat is
discharged and deleted. Cite that file, not this one, for the carrier.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct MonoidalCategory CartesianMonoidalCategory

namespace PiTensorProduct

section AffineCarrier

variable (k : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra k A] (n : ℕ)

/-! ## §1. The comparison

`tensorPowerFanIsLimit` says the opped cofan is a limit fan in `(Under k)ᵒᵖ`; `productIsProduct`
says `∏ᶜ` with its `Pi.π` is another. Two limits of the same diagram, so one iso — and
`conePointUniqueUpToIso_hom_comp` is the law that lets one compute with it. -/

/-- **The affine carrier, named.** The `n`-fold product of `op (mkUnder k A)` in `(Under k)ᵒᵖ` —
the object `SymPowColimit.permDiagram` is built on — is `op` of the tensor power.

Geometrically: `(Spec_k A)^n = Spec_k (A^{⊗ n})`, which is the input Milne's affine symmetric
power is a quotient of. -/
noncomputable def tensorPowerOpIsoPiObj [HasProduct
    (fun _ : Fin n => Opposite.op (CommRingCat.mkUnder k A))] :
    Opposite.op (CommRingCat.mkUnder k (⨂[k] _ : Fin n, A))
      ≅ ∏ᶜ (fun _ : Fin n => Opposite.op (CommRingCat.mkUnder k A)) :=
  (tensorPowerFanIsLimit k A n).conePointUniqueUpToIso (productIsProduct _)

/-- **The transport law.** The comparison carries the categorical projection `Pi.π i` to `op`
of the `i`-th structural inclusion `singleAlgHom i`.

This is the clause that makes `tensorPowerOpIsoPiObj` computable with. An isomorphism of
objects alone would let one restate things and prove nothing. -/
theorem tensorPowerOpIsoPiObj_hom_π [HasProduct
    (fun _ : Fin n => Opposite.op (CommRingCat.mkUnder k A))] (i : Fin n) :
    (tensorPowerOpIsoPiObj k A n).hom
        ≫ Pi.π (fun _ : Fin n => Opposite.op (CommRingCat.mkUnder k A)) i
      = ((tensorPowerCofan k A n).inj i).op :=
  (tensorPowerFanIsLimit k A n).conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨i⟩

/-! ## §2. The actions match

`MonObj.permAut` permutes the factors of the categorical product; `permAlgHom` permutes the
tensor factors. The comparison intertwines them — with the `e⁻¹` that this cone carries in four
places now (`permAlgHom_comp`, `permEnd`, `invEquivalence_comp_op_map`,
`tensorPowerCofan_inj_permAlgHom`).

**Read the inversion off the two projection laws, and do not guess it — this was got backwards
on the first attempt here, as it had been once before in this cone.**
`permAut C σ ≫ Pi.π i = Pi.π (σ i)` **raises** the index, while
`inj i ≫ permAlgHom e = inj (e⁻¹ i)` **lowers** it. So matching them at the same slot forces
`permAut e` to correspond to `permAlgHom e⁻¹`, not to `permAlgHom e`: the statement below
carries `e⁻¹` on the algebra side. Writing `permAlgHom e` there typechecks as a *statement* and
leaves the residual goal `inj (e i) = inj (e⁻¹ i)` after `Pi.hom_ext`, true only at an
involution. The kernel caught it; resemblance between a homomorphism and an
anti-homomorphism does not transport a variance. -/

/-- **The action match at the product.** Across the comparison, the factor-permuting
automorphism `permAut e` of the `n`-fold product in `(Under k)ᵒᵖ` is `op (permAlgHom e⁻¹)` on
the tensor power. See the section note for why the inverse is forced and not a convention.

So the identification of the carrier is an identification of `S_n`-objects, not merely of
objects — the distinction this project records as "groups agree ≠ maps agree". -/
theorem permAut_eq_op_permAlgHom [HasProduct
    (fun _ : Fin n => Opposite.op (CommRingCat.mkUnder k A))]
    [CartesianMonoidalCategory (Under k)ᵒᵖ] (e : Equiv.Perm (Fin n)) :
    (tensorPowerOpIsoPiObj k A n).hom
        ≫ MonObj.permAut (Opposite.op (CommRingCat.mkUnder k A)) e
      = ((permAlgHom (k : Type u) A e⁻¹).toUnder).op ≫ (tensorPowerOpIsoPiObj k A n).hom := by
  refine Pi.hom_ext _ _ (fun i => ?_)
  rw [Category.assoc, MonObj.permAut_π, Category.assoc, tensorPowerOpIsoPiObj_hom_π,
    tensorPowerOpIsoPiObj_hom_π]
  have h := congrArg Quiver.Hom.op (tensorPowerCofan_inj_permAlgHom k A n e⁻¹ i)
  rw [show (e⁻¹).symm = e from rfl] at h
  exact h.symm

end AffineCarrier

end PiTensorProduct
