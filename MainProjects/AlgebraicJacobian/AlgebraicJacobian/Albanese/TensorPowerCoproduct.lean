/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowTensorAction

/-!
# The `n`-fold tensor power is the `n`-ary coproduct of algebras

`Albanese/StableAffineCoverGroup.lean` lists four inputs a `Scheme.GlueData` for `Sym^n C`
needs. Item 3 is the comparison

> the `n`-ary coproduct of `R`-algebras **is** the `n`-fold tensor power `⨂[R] i, A i`,

which two previous sessions on this leg recorded as absent from mathlib and unbuilt in AJC,
with the consequence that `SymPowColimit.symPowData_affineAlgebra` (whose diagram is built
from the `n`-ary **coproduct** in `Under k`) and the whole `PiTensorProduct` layer
(`Albanese/SymPowTensorAction.lean`, `SymPowInvariants*.lean`) were provably *about different
objects*. That mismatch is what this file removes.

## What was actually missing, and what was not

Mathlib has the **binary** case as a pushout (`CommRingCat.pushoutCoconeIsColimit`,
`Mathlib/Algebra/Category/Ring/Constructions.lean`) and nothing `n`-ary. But it turns out that
*both halves of the `n`-ary universal property are already in mathlib*, unbundled and not
labelled as a colimit:

* **uniqueness** is `PiTensorProduct.algHom_ext` — two algebra maps out of a finite tensor
  power agree as soon as they agree on each `PiTensorProduct.singleAlgHom i`, the inclusion
  `a ↦ 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1`. That is exactly `Cofan.IsColimit`'s uniqueness clause;
* **existence** is one application of `PiTensorProduct.liftAlgHom` to the multilinear map
  `x ↦ ∏ i, f i (x i)`, and is `coprodLift` below.

So the honest description of item 3 is not "mathlib lacks the `n`-ary comparison" but "mathlib
has it in pieces, under names that do not mention colimits". The only mathematical content
supplied here is the multilinearity of `x ↦ ∏ i, f i (x i)`, which is
`Finset.prod_update_of_mem` three times.

**Where commutativity is load-bearing.** `coprodLift` needs the target `S` to be
*commutative*: the product `∏ i, f i (x i)` must be independent of the order of the factors,
and multiplicativity `f (x * y) = f x * f y` is `Finset.prod_mul_distrib`. This is why the
statement is about the coproduct in **commutative** algebras — which is the category the
affine symmetric power lives in — and not a coproduct in all `R`-algebras, where the tensor
power is *not* the coproduct. A reader coming from the noncommutative case should not read
this file as more general than it is.

## Main results

* `PiTensorProduct.coprodLift` — the lift of a family `f : ∀ i, A i →ₐ[R] S` into a
  commutative `S`, together with `coprodLift_tprod` and
  `coprodLift_comp_singleAlgHom` (its defining equation).
* `PiTensorProduct.existsUnique_coprodLift` — the `n`-ary coproduct universal property as a
  single `∃!` statement: this is the form a colimit consumer wants.
* `PiTensorProduct.coprodLift_permAlgHom` — **the equivariance that item 3 actually asks
  for**, and the reason this file imports `SymPowTensorAction`: the comparison intertwines
  the factor-permutation action `permAlgHom` on the tensor power with *reindexing the family*.
  Without it the identification would be an isomorphism of objects that does not respect the
  `S_n`-actions, and so would say nothing about symmetric powers (the failure mode recorded
  in this leg's memory as "groups agree ≠ maps agree").

## What this does *not* close

Item 3 of the four-item bill, only. In particular:

* it does **not** build the `Under k`-valued or `CommRingCat`-valued cofan and prove
  `IsColimit` of it. The algebra-level `∃!` is the mathematical content; crossing into
  `(Under k)ᵒᵖ` is bookkeeping this file deliberately leaves to its consumer, since
  `SymPowColimit`'s §5 caveat about which category is which is exactly where a previous
  session went wrong;
* `HasColimit (permDiagram C n)` for the curve remains open, and `AlbaneseUP.lean`'s six
  sorries are unchanged.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94 (the affine symmetric power
`(A^{⊗ n})^{S_n}`). Mathlib's binary comparison:
`Mathlib/Algebra/Category/Ring/Constructions.lean`.
-/

set_option autoImplicit false

universe u v w

open TensorProduct

namespace PiTensorProduct

section Coproduct

variable {R : Type u} {ι : Type v} {A : ι → Type w} {S : Type*}
  [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [CommRing S] [Algebra R S]

section Mk

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Postcomposing a family of algebra maps commutes with `Function.update`.** The one
bookkeeping fact behind multilinearity of `x ↦ ∏ i, f i (x i)`: changing the `i`-th entry of
the tuple changes the `i`-th factor of the product and nothing else. -/
private theorem comp_update (f : (i : ι) → (A i →ₐ[R] S)) (x : ∀ i, A i) (i : ι) (v : A i) :
    (fun j => f j (Function.update x i v j))
      = Function.update (fun j => f j (x j)) i (f i v) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- **The multilinear map underlying the coproduct lift**, `x ↦ ∏ i, f i (x i)`.

Both multilinearity clauses are `comp_update` followed by `Finset.prod_update_of_mem`, which
isolates the `i`-th factor; then `map_add` / `map_smul` of `f i` and distributivity. -/
noncomputable def coprodMultilinear (f : (i : ι) → (A i →ₐ[R] S)) :
    MultilinearMap R A S :=
  MultilinearMap.mk (fun x => ∏ i, f i (x i))
    (by
      intro _ x i a b
      rw [comp_update f x i (a + b), comp_update f x i a, comp_update f x i b,
        Finset.prod_update_of_mem (Finset.mem_univ i),
        Finset.prod_update_of_mem (Finset.mem_univ i),
        Finset.prod_update_of_mem (Finset.mem_univ i), map_add, add_mul])
    (by
      intro _ x i c a
      rw [comp_update f x i (c • a), comp_update f x i a,
        Finset.prod_update_of_mem (Finset.mem_univ i),
        Finset.prod_update_of_mem (Finset.mem_univ i), map_smul, smul_mul_assoc])

omit [DecidableEq ι] in
@[simp]
theorem coprodMultilinear_apply (f : (i : ι) → (A i →ₐ[R] S)) (x : ∀ i, A i) :
    coprodMultilinear f x = ∏ i, f i (x i) := rfl

/-- **The coproduct lift.** A family of algebra maps `f i : A i →ₐ[R] S` into a
*commutative* `S` induces an algebra map out of the tensor power, sending
`a_1 ⊗ ⋯ ⊗ a_n` to `f_1(a_1) ⋯ f_n(a_n)`.

Unitality is `∏ i, f i 1 = 1`; multiplicativity is `Finset.prod_mul_distrib`, and **this is
where commutativity of `S` is used** — see the module header. -/
noncomputable def coprodLift (f : (i : ι) → (A i →ₐ[R] S)) :
    (⨂[R] i, A i) →ₐ[R] S :=
  liftAlgHom (coprodMultilinear f)
    (by simp)
    (by
      intro x y
      simp only [coprodMultilinear_apply, Pi.mul_apply, map_mul, Finset.prod_mul_distrib])

omit [DecidableEq ι] in
@[simp]
theorem coprodLift_tprod (f : (i : ι) → (A i →ₐ[R] S)) (x : ∀ i, A i) :
    coprodLift f (tprod R x) = ∏ i, f i (x i) := by
  simp [coprodLift]

/-- **The defining equation of the coproduct lift.** Precomposing with the `i`-th structural
inclusion `singleAlgHom i` recovers `f i`: every factor other than the `i`-th contributes
`f j 1 = 1`. -/
theorem coprodLift_comp_singleAlgHom (f : (i : ι) → (A i →ₐ[R] S)) (i : ι) :
    (coprodLift f).comp (singleAlgHom i) = f i := by
  ext a
  rw [AlgHom.comp_apply, singleAlgHom_apply, coprodLift_tprod]
  have h : (fun j => f j (MonoidHom.mulSingle A i a j))
      = Function.update (fun _ => (1 : S)) i (f i a) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

set_option linter.unusedFintypeInType false in
/-- **The `n`-ary coproduct universal property of the tensor power, as one statement.**

For a finite family of commutative `R`-algebras `A i` and a commutative `R`-algebra `S`,
algebra maps out of `⨂[R] i, A i` correspond to families of algebra maps out of the `A i`:
there is a *unique* `u` with `u ∘ singleAlgHom i = f i` for every `i`.

This is the shape a `Cofan.IsColimit` consumer wants. Existence is `coprodLift`; uniqueness
is mathlib's `algHom_ext`, which is the coproduct uniqueness clause under another name.

The `[Fintype ι]` binder does not appear in the statement's *type* (the linter says so) but is
load-bearing in the proof: `coprodLift`'s product `∏ i, f i (x i)` needs it. `Finite` would do
after `Fintype.ofFinite`, but then the witness would not be syntactically `coprodLift f`, which
is what call sites rewrite with. -/
theorem existsUnique_coprodLift (f : (i : ι) → (A i →ₐ[R] S)) :
    ∃! u : (⨂[R] i, A i) →ₐ[R] S, ∀ i, u.comp (singleAlgHom i) = f i :=
  ⟨coprodLift f, coprodLift_comp_singleAlgHom f,
    fun _ hu => algHom_ext fun i => (hu i).trans (coprodLift_comp_singleAlgHom f i).symm⟩

end Mk

/-! ### Equivariance: the comparison respects the `S_n`-actions

The identification above is an isomorphism of *objects*. For the symmetric power it must also
match the actions on the two sides — otherwise it is the "groups agree but the maps do not"
failure this project has hit before, and it would license nothing about `(A^{⊗ n})^{S_n}`.

The statement is the natural one: permuting the factors of the tensor power and then lifting
`f` is the same as lifting the *reindexed* family. Since all the `A i` are the same algebra
`A` in the symmetric-power application, "reindexed family" is just `f ∘ e`. -/

section Equivariance

-- `A'` must live in the *ring's* universe `u`: `SymPowTensorAction.permAlgHom` is stated with
-- `(R : Type u) (A : Type u)`, so a `Type w` algebra cannot be permuted by it. Matching the
-- binder here rather than generalising `permAlgHom` keeps this file additive over that one.
-- No `DecidableEq ι`: the proof opens with `classical`, so it would be an unused binder in the
-- statement (and the linter rightly rejects it).
variable {A' : Type u} [CommRing A'] [Algebra R A'] [Fintype ι]

/-- **The comparison is equivariant.** For a constant family `A' i = A'`, permuting the
tensor factors along `e` and then lifting `f` agrees with lifting the family reindexed along
`e⁻¹`:

`coprodLift f ∘ permAlgHom e = coprodLift (f ∘ e⁻¹)`.

**Read the variance, and do not guess it.** The first draft of this lemma stated `f ∘ e` on
the right and was *false*: the residual goal was `f (e⁻¹ i) a = f (e i) a`, which holds only
at an involution. On generators, `permAlgHom e` sends `tprod x` to `tprod (x ∘ e)`, so the
lift becomes `∏ i, f i (x (e i))`; reindexing `j = e i` turns that into
`∏ j, f (e⁻¹ j) (x j)`, which is the lift of `f ∘ e⁻¹`. The inverse here is the *same*
`permAlgHom` anti-homomorphism bookkeeping that `SymPowTensorAction.permAlgHom_comp` records
and that `permMulSemiringAction` absorbs by acting through `σ⁻¹`.

This is the clause that makes the identification usable for symmetric powers rather than
merely true: without it the two sides carry unrelated `S_n`-actions, and an isomorphism of
objects alone licenses nothing about `(A^{⊗ n})^{S_n}`. -/
theorem coprodLift_permAlgHom (f : ι → (A' →ₐ[R] S)) (e : Equiv.Perm ι) :
    (coprodLift (A := fun _ : ι => A') f).comp (permAlgHom R A' e)
      = coprodLift (A := fun _ : ι => A') (fun i => f (e.symm i)) := by
  classical
  refine algHom_ext fun i => ?_
  ext a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, singleAlgHom_apply, permAlgHom_tprod,
    coprodLift_tprod, AlgHom.comp_apply, singleAlgHom_apply, coprodLift_tprod]
  -- Both sides are a product with a single nontrivial factor; identify which slot.
  have hl : (fun j => f j (MonoidHom.mulSingle (fun _ : ι => A') i a (e j)))
      = Function.update (fun _ => (1 : S)) (e.symm i) (f (e.symm i) a) := by
    funext j
    by_cases hj : j = e.symm i
    · subst hj; simp
    · have hne : e j ≠ i := fun hc => hj (by rw [← hc, Equiv.symm_apply_apply])
      simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hne]
  have hr : (fun j => f (e.symm j) (MonoidHom.mulSingle (fun _ : ι => A') i a j))
      = Function.update (fun _ => (1 : S)) i (f (e.symm i) a) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, Pi.mulSingle_eq_of_ne hj]
  rw [hl, hr, Finset.prod_update_of_mem (Finset.mem_univ _),
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

omit [Fintype ι] in
/-- **The action on the coprojections: permuting factors relabels the inclusions.**

`permAlgHom e ∘ singleAlgHom i = singleAlgHom (e⁻¹ i)`.

This is the statement that matches the two `S_n`-actions *at the level of the coproduct
structure*, and it is the one "matching the permutation action to `permAlgHom`" really asks
for: `coprodLift_permAlgHom` above relates the lift to itself under reindexing, with both
sides inside `PiTensorProduct`, whereas this one says how the action moves the `i`-th
coprojection — the datum a cofan is built from.

Note it carries `e⁻¹`, independently confirming the variance of `coprodLift_permAlgHom`:
`permAlgHom e` sends `tprod x` to `tprod (x ∘ e)`, so the tuple `mulSingle i a` is hit at the
slot `j` with `e j = i`. -/
theorem permAlgHom_comp_singleAlgHom [DecidableEq ι] (e : Equiv.Perm ι) (i : ι) :
    (permAlgHom R A' e).comp (singleAlgHom (R := R) (A := fun _ : ι => A') i)
      = singleAlgHom (R := R) (A := fun _ : ι => A') (e.symm i) := by
  classical
  ext a
  rw [AlgHom.comp_apply, singleAlgHom_apply, permAlgHom_tprod, singleAlgHom_apply]
  congr 1
  funext j
  by_cases hj : j = e.symm i
  · subst hj; simp
  · have hne : e j ≠ i := fun hc => hj (by rw [← hc, Equiv.symm_apply_apply])
    simp [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hne]

end Equivariance

end Coproduct

end PiTensorProduct
