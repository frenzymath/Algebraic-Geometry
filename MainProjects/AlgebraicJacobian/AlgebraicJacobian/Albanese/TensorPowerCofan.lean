/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.TensorPowerCoproduct

/-!
# The tensor power **is** the `n`-ary coproduct, packaged as a `Cofan` in `Under k`

`Albanese/TensorPowerCoproduct.lean` proved the `n`-ary coproduct universal property of
`⨂[k] _ : Fin n, A` at the level of algebra homomorphisms (`existsUnique_coprodLift`),
together with both equivariance clauses. It deliberately stopped short of the categorical
crossing, and `Albanese/StableAffineCoverGroup.lean`'s four-item bill therefore recorded item
3 as **partial**: the mathematics was proved, the `Cofan`/`IsColimit` packaging was not, and
`SymPowColimit.symPowData_affineAlgebra` — whose diagram is built from the `n`-fold product in
`(Under k)ᵒᵖ`, i.e. the `n`-fold *coproduct* in `Under k` — consumed none of it.

This file writes that packaging. It is bookkeeping, not mathematics: every clause is one of
the algebra-level statements pushed through `AlgHom.toUnder`.

## The one trap, measured rather than guessed

`CommRingCat.toAlgHom` does **not** produce the algebra map you want out of `mkUnder k A`. It
is typed over `CommRingCat.instAlgebraCarrierRight`, i.e. `RingHom.toAlgebra (algebraMap k A)`
rebuilt from the structure morphism, not over the ambient `[Algebra k A]` instance the tensor
power is formed with. The two are equal but not syntactically the same instance, so
`toAlgHom f : ↑(mkUnder k A) →ₐ[k] ↑B` will not unify with `A →ₐ[k] ↑B`. `algHomOfMkUnderHom`
below is the version over the ambient instance; its proof is `Under.w` and one `congrArg`.

The other direction needs nothing: `AlgHom.toUnder` already lands in `mkUnder k ↑B`, and
`mkUnder k ↑B = B` holds by `rfl` for every `B : Under k`, so a lift out of the tensor power
is a morphism into `B` on the nose.

## Main results

* `algHomOfMkUnderHom` — the missing direction of the bridge (see the trap above), with
  `algHomOfMkUnderHom_toUnder` and `toUnder_algHomOfMkUnderHom` making it a bijection.
* `tensorPowerCofan` — the cofan with vertex `mkUnder k (⨂[k] _ : Fin n, A)` and coprojections
  `singleAlgHom i`.
* `tensorPowerCofanIsColimit` — **the packaging**: that cofan is a colimit. Existence is
  `coprodLift`, uniqueness is `PiTensorProduct.algHom_ext`.
* `hasCoproduct_mkUnder` — the `HasCoproduct` form, and `tensorPowerIsoCoproduct`,
  identifying `⨂[k] _ : Fin n, A` with `∐ᶜ` of `n` copies of `A` as `k`-algebras.
* `tensorPowerFanIsLimit` — the dual, in `(Under k)ᵒᵖ`: the same data is the `n`-ary
  **product** there, which is the category and variance
  `SymPowColimit.symPowData_affineAlgebra` works in.
* `tensorPowerCofan_inj_permAlgHom` — the equivariance, on the coprojections: permuting the
  tensor factors along `e` relabels the `i`-th coprojection to the `e⁻¹ i`-th. This is
  `permAlgHom_comp_singleAlgHom` in `Under k`, and it is what makes the identification an
  identification *of `S_n`-objects* rather than merely of objects.

## Scope — what this does and does not close

**Does**: item 3 of `StableAffineCoverGroup.lean`'s four-item bill, in full. The bill now
reads 3 supplied, 1 open.

**Does not**: build the glue data, and does not close `HasColimit (permDiagram C n)` for the
curve. `AlbaneseUP.lean`'s six sorries are unchanged by this file, and
`albanese_universal_property` still reports `sorryAx`. What changes is that the affine chart's
carrier is now a *named* object of `Under k` with its universal property in categorical form,
rather than an unnamed colimit — which was the gap `SymPowColimit.lean` §5 flagged with "**The
carrier is not named in Lean.**" That caveat was discharged and deleted later the same round
(run 0069 r7) by `SymPowAffineQuotient.colimitPermDiagramIsoFixed`; this file is one of its
inputs, not its closure.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94. Mathlib's binary comparison is
`CommRingCat.pushoutCoconeIsColimit`; the `Under`-algebra bridge is
`Mathlib/Algebra/Category/Ring/Under/Basic.lean`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TensorProduct

namespace PiTensorProduct

section UnderCofan

variable (k : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra k A] (n : ℕ)

/-! ## §1. The bridge, in the direction mathlib does not supply

`AlgHom.toUnder` turns an algebra map into a morphism of `Under k`. The reverse — a morphism
out of `mkUnder k A` as an algebra map over the *ambient* instance — is the one that needs
writing; see the module header for why `CommRingCat.toAlgHom` does not serve. -/

/-- **A morphism out of `mkUnder k A` as an algebra map, over the ambient instance.**

Unlike `CommRingCat.toAlgHom`, the source's `Algebra k`-structure here is the one `A` was
given, not the one rebuilt from the structure morphism of `mkUnder k A`. The `commutes'`
clause is exactly the triangle `Under.w`. -/
noncomputable def algHomOfMkUnderHom {B : Under k} (f : CommRingCat.mkUnder k A ⟶ B) :
    A →ₐ[k] B where
  __ := f.right.hom
  commutes' r :=
    congrArg (fun (g : k ⟶ B.right) => g.hom r) (f.w : (CommRingCat.mkUnder k A).hom ≫ _ = B.hom)

@[simp]
theorem algHomOfMkUnderHom_apply {B : Under k} (f : CommRingCat.mkUnder k A ⟶ B) (a : A) :
    algHomOfMkUnderHom k A f a = f.right a := rfl

/-- The bridge is a section of `AlgHom.toUnder`.

Stated pointwise rather than as an equality of algebra maps: the two sides are typed over
different (equal, not syntactically identical) `Algebra k`-instances on the target — the trap
of the module header, appearing here as well. Pointwise both sides are literally `f a`. -/
@[simp]
theorem algHomOfMkUnderHom_toUnder {B : Type u} [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (a : A) :
    algHomOfMkUnderHom k A f.toUnder a = f a := rfl

/-- …and a retraction of it: a morphism out of `mkUnder k A` is recovered from its algebra
map. Both directions are `rfl`, which is the point of routing through the ambient instance. -/
@[simp]
theorem toUnder_algHomOfMkUnderHom {B : Under k} (f : CommRingCat.mkUnder k A ⟶ B) :
    (algHomOfMkUnderHom k A f).toUnder = f := rfl

/-! ## §2. The cofan and its colimit property

Nothing here is new mathematics: `desc` is `coprodLift`, `fac` is
`coprodLift_comp_singleAlgHom`, and `uniq` is `PiTensorProduct.algHom_ext`. -/

/-- **The cofan exhibiting `⨂[k] _ : Fin n, A` as the `n`-ary coproduct** of `n` copies of `A`
in `Under k`, with the structural inclusions `singleAlgHom i : a ↦ 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1` as
coprojections. -/
noncomputable def tensorPowerCofan : Cofan (fun _ : Fin n => CommRingCat.mkUnder k A) :=
  Cofan.mk (CommRingCat.mkUnder k (⨂[k] _ : Fin n, A))
    (fun i => (singleAlgHom (R := k) (A := fun _ : Fin n => A) i).toUnder)

@[simp]
theorem tensorPowerCofan_inj (i : Fin n) :
    (tensorPowerCofan k A n).inj i
      = (singleAlgHom (R := k) (A := fun _ : Fin n => A) i).toUnder := rfl

/-- **The packaging: the tensor power is the `n`-ary coproduct in `Under k`.**

This is the statement `Albanese/TensorPowerCoproduct.lean` deliberately left to its consumer
and that `StableAffineCoverGroup.lean`'s bill recorded as the missing half of item 3. Both
clauses are the algebra-level facts pushed through the bridge of §1. -/
noncomputable def tensorPowerCofanIsColimit : IsColimit (tensorPowerCofan k A n) :=
  Cofan.IsColimit.mk _
    (fun t => (coprodLift (R := k) (A := fun _ : Fin n => A)
      (fun i => algHomOfMkUnderHom k A (t.inj i))).toUnder)
    (fun t i => by
      refine CommRingCat.mkUnder_ext (fun a => ?_)
      change (coprodLift (R := k) (A := fun _ : Fin n => A)
        (fun i => algHomOfMkUnderHom k A (t.inj i)))
          (singleAlgHom (R := k) (A := fun _ : Fin n => A) i a) = _
      rw [← AlgHom.comp_apply, coprodLift_comp_singleAlgHom]
      rfl)
    (fun t m hm => by
      refine CommRingCat.mkUnder_ext (fun x => ?_)
      have h : algHomOfMkUnderHom k _ m
          = coprodLift (R := k) (A := fun _ : Fin n => A)
            (fun i => algHomOfMkUnderHom k A (t.inj i)) := by
        refine algHom_ext (fun i => ?_)
        ext a
        rw [AlgHom.comp_apply, coprodLift_comp_singleAlgHom]
        exact congrArg (fun (g : CommRingCat.mkUnder k A ⟶ t.pt) => g.right a) (hm i)
      exact congrArg (fun (g : (⨂[k] _ : Fin n, A) →ₐ[k] t.pt) => g x) h)

/-- The `HasCoproduct` form. -/
theorem hasCoproduct_mkUnder : HasCoproduct (fun _ : Fin n => CommRingCat.mkUnder k A) :=
  ⟨⟨⟨tensorPowerCofan k A n, tensorPowerCofanIsColimit k A n⟩⟩⟩

/-- **The identification of objects**: `⨂[k] _ : Fin n, A` is `∐ᶜ` of `n` copies of `A`, as an
object of `Under k`. -/
noncomputable def tensorPowerIsoCoproduct
    [HasCoproduct (fun _ : Fin n => CommRingCat.mkUnder k A)] :
    CommRingCat.mkUnder k (⨂[k] _ : Fin n, A)
      ≅ ∐ (fun _ : Fin n => CommRingCat.mkUnder k A) :=
  (tensorPowerCofanIsColimit k A n).coconePointUniqueUpToIso (colimit.isColimit _)

/-! ## §3. Dually, in `(Under k)ᵒᵖ`: the same data is the `n`-ary **product**

`SymPowColimit.symPowData_affineAlgebra` works in `(Under k)ᵒᵖ` and forms `∏ᶜ` there. Under
`op` that product is this coproduct, so the fan below is the object its `permDiagram` is built
on. -/

/-- **The tensor power as the `n`-ary product in `(Under k)ᵒᵖ`** — the category and variance
`SymPowColimit.symPowData_affineAlgebra` works in. -/
noncomputable def tensorPowerFanIsLimit :
    IsLimit (tensorPowerCofan k A n).op :=
  Cofan.IsColimit.op (tensorPowerCofanIsColimit k A n)

/-- The `HasProduct` form in `(Under k)ᵒᵖ`. -/
theorem hasProduct_op_mkUnder :
    HasProduct (fun i : Fin n => Opposite.op ((fun _ : Fin n => CommRingCat.mkUnder k A) i)) :=
  ⟨⟨⟨(tensorPowerCofan k A n).op, tensorPowerFanIsLimit k A n⟩⟩⟩

/-! ## §4. The equivariance, on the coprojections

An identification of objects licenses nothing about symmetric powers; the actions must match.
At the level of a cofan the action is visible on the coprojections, and the statement is
`TensorPowerCoproduct.permAlgHom_comp_singleAlgHom` in `Under k`.

**Read the `e⁻¹`.** `permAlgHom e` sends `tprod x` to `tprod (x ∘ e)`, so the tuple with `a` in
slot `i` is hit at the slot `j` with `e j = i`. The inversion is the same convention
`SymPowTensorAction.permAlgHom_comp`, `SymPowColimit.permEnd` and
`SymPowInvariantsUnder.invEquivalence_comp_op_map` each carry. -/

/-- **The comparison respects the `S_n`-actions, at the coprojections.**

`inj i ≫ permAlgHom e = inj (e⁻¹ i)`: permuting the tensor factors along `e` relabels the
`i`-th coprojection to the `e⁻¹ i`-th. -/
theorem tensorPowerCofan_inj_permAlgHom (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (tensorPowerCofan k A n).inj i ≫ (permAlgHom (k : Type u) A e).toUnder
      = (tensorPowerCofan k A n).inj (e.symm i) := by
  refine CommRingCat.mkUnder_ext (fun a => ?_)
  exact congrArg (fun (g : A →ₐ[k] (⨂[k] _ : Fin n, A)) => g a)
    (permAlgHom_comp_singleAlgHom (R := k) (A' := A) e i)

end UnderCofan

end PiTensorProduct
