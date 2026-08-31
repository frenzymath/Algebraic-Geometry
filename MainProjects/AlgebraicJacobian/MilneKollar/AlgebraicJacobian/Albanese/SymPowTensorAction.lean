/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.SymPowInvariants

/-!
# Milne's `(A^{⊗ n})^{S_n}`: the symmetric group acting on a tensor power of a ring

`Albanese/SymPowInvariants.lean` proved that the invariant subring `A^G` **is** the limit of
a group action in `CommRingCat`, hence a colimit — a quotient — in `CommRingCatᵒᵖ`. Its §4
then listed three things that identification still lacked, and the second was this:

> The specialisation to Milne's actual ring. `G := Equiv.Perm (Fin n)` acting on the
> `n`-fold tensor power `A^{⊗ n}` is the case Milne uses; the `S_n`-action on a tensor
> power of a commutative *ring* is not built here (mathlib's symmetric API is for
> modules — `PiTensorProduct.reindex` is a *linear* equiv).

This file supplies it. Mathlib has the commutative ring and `R`-algebra structure on
`⨂[R] i, A i` (`Mathlib/RingTheory/PiTensorProduct.lean`) and it has factor permutation as
a *linear* equivalence, but nothing upgrades the permutation to a ring or algebra map, so
`MulSemiringAction (Equiv.Perm ι) (⨂[R] _ : ι, A)` does not synthesize. Without that
instance `FixedPoints.subring`/`subalgebra` cannot even be *stated* at the tensor power, so
Milne's formula was not expressible in the tree.

## Main results

* `PiTensorProduct.permAlgHom` — factor permutation as an `R`-**algebra** homomorphism of
  `⨂[R] _ : ι, A`, built from `liftAlgHom` on the reindexed `tprod`.
* `PiTensorProduct.permAlgHom_comp` — the composition law, and note its **variance**:
  `permAlgHom σ ∘ permAlgHom τ = permAlgHom (τ * σ)`, an *anti*-homomorphism.
* `PiTensorProduct.permAlgEquiv` — hence the algebra automorphism.
* `PiTensorProduct.permMulSemiringAction` — the left `S_n`-action, taking `σ` to
  `permAlgHom σ⁻¹`. The inverse is forced by the previous item, exactly as
  `SymPowColimit.permEnd` needs `σ⁻¹` on the geometric side.
* `PiTensorProduct.permSMulCommClass` — the action commutes with scalars (one `map_smul`).
  `FixedPoints.subalgebra` needs this *in addition to* the `MulSemiringAction`, and mathlib
  supplies neither at a tensor power; it is also what makes the action a diagram over the
  base ring (`Albanese/SymPowInvariantsUnder.lean`).
* `symTensorPowSubalgebra R A` — **Milne's `(A^{⊗ n})^{S_n}`**, as an `R`-subalgebra, with
  `mem_symTensorPowSubalgebra_iff` and `symTensorPowSubalgebra_toSubring`. The universal
  property is *not* restated here as an algebra statement; it arrives in categorical form
  through the next item, which is where the limit/colimit property is proved.
* `hasLimit_actionDiagram_symTensorPow` / `hasColimit_actionDiagram_op_symTensorPow` — the
  same fact as a limit in `CommRingCat` and a colimit in `CommRingCatᵒᵖ`, obtained by
  instantiating `SymPowInvariants`' general theorems at this action. This is the first
  place in the tree where Milne's affine carrier appears as a named object with a proved
  quotient property.

## Characteristic-free, and no finiteness on the ring

Nothing here averages over the group, so no `n!` is inverted and the statements hold in
every characteristic — which matters, since `Sym^g C` is wanted over an arbitrary
algebraically closed `k̄` and `g!` may vanish there.

Where finiteness of `ι` *is* needed, precisely (an earlier version of this paragraph said the
action needs none, which is false — `permMulSemiringAction ℤ (ι := ℕ) ℤ` fails to synthesize
`Finite ℕ`): `permAlgHom`, `symTensorPowSubalgebra`, `mem_symTensorPowSubalgebra_iff` and
`tprod_const_mem_symTensorPowSubalgebra` need none; `permAlgHom_comp`, `permAlgHom_one`,
`permAlgEquiv` and hence the **action** do, because `PiTensorProduct.algHom_ext` (extensionality
over `singleAlgHom`) requires `[Finite ι]`. `Fin n` in particular enters only when specialising
to Milne's `n`-fold power.

## Scope — what this is not

This is **affine commutative algebra**. It does not construct `Sym^n C` for a curve, and it
does not close `SymPowInvariants` §4's other two items:

* the curve case still needs `HasColimit (permDiagram C g)` in `Over (Spec k̄)`, i.e. the
  gluing (`Albanese/SymPowColimit.lean` §6);
* the **category** caveat stands. `SymPowColimit`'s affine inhabitation statement
  `symPowData_affineAlgebra` lives in `(Under k)ᵒᵖ`; everything here, like
  `SymPowInvariants`, lives in `CommRingCat`/`CommRingCatᵒᵖ` with no base ring in the
  *category*, even though the ring statements are `R`-algebra statements. Bridging those
  two remains open, so no declaration in `SymPowColimit.lean` consumes anything below.

Read this file, then, as: *Milne's affine carrier is now nameable and its universal
property is proved*, not as *Milne III.3 Proposition 3.1 is formalised*.

## References

Milne, *Abelian Varieties*, §III.3 Proposition 3.1, p. 94 (the symmetric power as
`Spec (A^{⊗ n})^{S_n}` glued over an affine cover). Mumford, *Abelian Varieties*, §II.7.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TensorProduct

namespace PiTensorProduct

section Action

variable (R : Type u) [CommRing R] {ι : Type v} (A : Type u) [CommRing A] [Algebra R A]

/-! ## §1. Factor permutation as an algebra homomorphism

The multilinear map `x ↦ tprod R (x ∘ e)` is unital and multiplicative on the nose, since
`(x * y) ∘ e = (x ∘ e) * (y ∘ e)` pointwise, so `liftAlgHom` applies with no side
conditions to discharge beyond those two equations. -/

/-- **Factor permutation, as an `R`-algebra endomorphism of the tensor power.**

`permAlgHom R A e` sends `a_1 ⊗ ⋯ ⊗ a_n` to the tuple reindexed along `e`:
`tprod x ↦ tprod (x ∘ e)`. Mathlib has this as a linear equivalence only
(`PiTensorProduct.reindex`); the algebra structure is what the invariant *subring* needs. -/
noncomputable def permAlgHom (e : Equiv.Perm ι) :
    (⨂[R] _ : ι, A) →ₐ[R] (⨂[R] _ : ι, A) :=
  liftAlgHom ((tprod R (s := fun _ : ι => A)).domDomCongr e)
    (by
      simp only [MultilinearMap.domDomCongr_apply]
      exact (one_def (R := R) (A := fun _ : ι => A)).symm)
    (by
      intro x y
      simp only [MultilinearMap.domDomCongr_apply]
      rw [show (fun i => (x * y) (e i)) = (fun i => x (e i)) * (fun i => y (e i)) from rfl,
        tprod_mul_tprod])

@[simp]
theorem permAlgHom_tprod (e : Equiv.Perm ι) (x : ι → A) :
    permAlgHom R A e (tprod R x) = tprod R (fun i => x (e i)) := by
  simp [permAlgHom]

variable [Finite ι]

/-- **The composition law, with its variance.** Reindexing along `e` then along `d`
reindexes along `e * d`… on the *tuples*, which is `d * e` read as permutations acting on
indices. Concretely `permAlgHom d ∘ permAlgHom e = permAlgHom (e * d)`: the assignment is an
*anti*-homomorphism, and that is why `permMulSemiringAction` below inserts an inverse.

The same bookkeeping appears on the geometric side in `SymPowColimit.permEnd`, for the
mirror-image reason (mathlib's `End` multiplication is `f * g = g ≫ f`). -/
theorem permAlgHom_comp (d e : Equiv.Perm ι) :
    (permAlgHom R A d).comp (permAlgHom R A e) = permAlgHom R A (e * d) := by
  classical
  ext i a
  simp [Equiv.Perm.mul_apply]

@[simp]
theorem permAlgHom_one : permAlgHom R A (1 : Equiv.Perm ι) = AlgHom.id R _ := by
  classical
  ext i a
  simp

/-- **Factor permutation as an algebra automorphism.** Its inverse is the permutation
`e⁻¹`, by `permAlgHom_comp` and `permAlgHom_one`. -/
noncomputable def permAlgEquiv (e : Equiv.Perm ι) :
    (⨂[R] _ : ι, A) ≃ₐ[R] (⨂[R] _ : ι, A) :=
  AlgEquiv.ofAlgHom (permAlgHom R A e) (permAlgHom R A e⁻¹)
    (by rw [permAlgHom_comp]; simp)
    (by rw [permAlgHom_comp]; simp)

@[simp]
theorem permAlgEquiv_tprod (e : Equiv.Perm ι) (x : ι → A) :
    permAlgEquiv R A e (tprod R x) = tprod R (fun i => x (e i)) :=
  permAlgHom_tprod R A e x

/-! ## §2. The action, with the inverse that makes it a left action

`permAlgHom` is an anti-homomorphism (`permAlgHom_comp`), so `σ • x := permAlgHom σ x` would
be a *right* action. Taking `σ • x := permAlgHom σ⁻¹ x` fixes the variance, and gives the
`MulSemiringAction` that `FixedPoints.subring` consumes.

This is the instance whose absence made Milne's formula unstateable: `FixedPoints.subring`
requires `MulSemiringAction G A`, and mathlib's `PiTensorProduct.reindex` — being only a
linear equivalence — cannot supply it. -/

/-- **The `S_ι`-action on the tensor power, as a `MulSemiringAction`.**

`σ • (a_1 ⊗ ⋯ ⊗ a_n) = a_{σ⁻¹ 1} ⊗ ⋯ ⊗ a_{σ⁻¹ n}`. The inverse is what turns the
anti-homomorphism `permAlgHom` into a left action; see `permAlgHom_comp`.

Deliberately **not** a global `instance`: the tensor power carries other group actions in
principle, and a global instance on `⨂[R] _ : ι, A` would fire during unrelated synthesis.
Consumers name it with `letI`, exactly as `SymPowInvariants` expects its
`MulSemiringAction` to be supplied. -/
@[implicit_reducible]
noncomputable def permMulSemiringAction :
    MulSemiringAction (Equiv.Perm ι) (⨂[R] _ : ι, A) where
  smul σ x := permAlgHom R A σ⁻¹ x
  one_smul x := by
    change permAlgHom R A (1 : Equiv.Perm ι)⁻¹ x = x
    rw [inv_one, permAlgHom_one]; rfl
  mul_smul σ τ x := by
    change permAlgHom R A (σ * τ)⁻¹ x = permAlgHom R A σ⁻¹ (permAlgHom R A τ⁻¹ x)
    have h := permAlgHom_comp R A (σ⁻¹) (τ⁻¹)
    rw [mul_inv_rev]
    exact (AlgHom.congr_fun h x).symm
  smul_zero σ := map_zero (permAlgHom R A σ⁻¹)
  smul_add σ x y := map_add (permAlgHom R A σ⁻¹) x y
  smul_one σ := map_one (permAlgHom R A σ⁻¹)
  smul_mul σ x y := map_mul (permAlgHom R A σ⁻¹) x y

/-- **The action commutes with scalars.** Immediate from `permAlgHom` being an *algebra*
hom, hence `R`-linear — one `map_smul`.

Needed because `FixedPoints.subalgebra` requires `[SMulCommClass G R B]` in addition to the
`MulSemiringAction`, and mathlib supplies neither at a tensor power. It is also the
hypothesis under which the action is a diagram in `Under R` rather than merely in
`CommRingCat`; see `Albanese/SymPowInvariantsUnder.lean`. -/
@[implicit_reducible]
noncomputable def permSMulCommClass :
    letI := permMulSemiringAction R (ι := ι) A
    SMulCommClass (Equiv.Perm ι) R (⨂[R] _ : ι, A) :=
  letI := permMulSemiringAction R (ι := ι) A
  ⟨fun σ r x => map_smul (permAlgHom R A σ⁻¹) r x⟩

/-- The action, unfolded. Note `(ι := ι)`: `permMulSemiringAction`'s index type is
implicit and does not appear in its explicit arguments, so a bare
`letI := permMulSemiringAction R A` in a *statement* leaves `ι` a metavariable and the
`HSMul` instance search gets stuck. Every `letI` of this action below names `ι`. -/
theorem permSmul_def (σ : Equiv.Perm ι) (x : ⨂[R] _ : ι, A) :
    letI := permMulSemiringAction R (ι := ι) A
    σ • x = permAlgHom R A σ⁻¹ x := rfl

/-! ## §3. Milne's carrier `(A^{⊗ n})^{S_n}`

Two forms, and the reason for both. `symTensorPowSubalgebra` states invariance *directly*
(`∀ σ, permAlgHom σ x = x`) so that the type mentions no action instance: with the action a
`letI`-supplied `def` rather than a global instance, a subalgebra whose very type depended on
it would be painful at every use site. `symTensorPowSubalgebra_toSubring` then identifies it
with `FixedPoints.subring` for the `letI` action, which is what
`Albanese/SymPowInvariants.lean` proves to be the limit.

Note the direction bookkeeping in that identification: `σ • x = permAlgHom σ⁻¹ x`, and
quantifying over all `σ` makes the inverse invisible — invariance under all of `S_n` is the
same set either way. That is the only content of the proof, and it is worth having as a
lemma because it is exactly where a sign error would hide. -/

/-- **Milne's `(A^{⊗ n})^{S_n}`, as an `R`-subalgebra.**

An element is in it iff every factor permutation fixes it. Stated with `permAlgHom`
directly, so that the type does not mention `permMulSemiringAction` — see the §3 header for
why that matters. -/
noncomputable def symTensorPowSubalgebra : Subalgebra R (⨂[R] _ : ι, A) where
  carrier := {x | ∀ σ : Equiv.Perm ι, permAlgHom R A σ x = x}
  mul_mem' hx hy σ := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, hx, hy]
  one_mem' σ := map_one _
  add_mem' hx hy σ := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, hx, hy]
  zero_mem' σ := map_zero _
  algebraMap_mem' r σ := AlgHom.commutes _ r

omit [Finite ι] in
@[simp]
theorem mem_symTensorPowSubalgebra_iff (x : ⨂[R] _ : ι, A) :
    x ∈ symTensorPowSubalgebra R A ↔ ∀ σ : Equiv.Perm ι, permAlgHom R A σ x = x := Iff.rfl

/-- **The two descriptions agree**: the directly-stated invariants are the fixed points of
the `MulSemiringAction`. The inverse in `permSmul_def` washes out because the condition
quantifies over the whole group.

This is the lemma that lets `Albanese/SymPowInvariants.lean`'s general theorems — stated for
`FixedPoints.subring` — be read as statements about Milne's carrier. -/
theorem symTensorPowSubalgebra_toSubring :
    letI := permMulSemiringAction R (ι := ι) A
    (symTensorPowSubalgebra R A).toSubring
      = FixedPoints.subring (⨂[R] _ : ι, A) (Equiv.Perm ι) := by
  letI := permMulSemiringAction R (ι := ι) A
  ext x
  constructor
  · intro h g
    exact h g⁻¹
  · intro h σ
    have hx : permAlgHom R A σ⁻¹⁻¹ x = x := h σ⁻¹
    rwa [inv_inv] at hx

omit [Finite ι] in
/-- **A tensor of a constant tuple is invariant** — the diagonal `a ⊗ ⋯ ⊗ a` lies in
Milne's carrier, since permuting a constant tuple does nothing.

Kept as a supply of elements: it exhibits the diagonal image of `A` inside the carrier, so
the invariants are not obviously just `algebraMap R`'s image. Note what this does **not**
prove — that the containment is *strict* for some `A`, which would need an element of
`⨂ A` shown outside the image of `R`, and no declaration here does that. So read it as a
witness that the carrier has describable elements, not as a non-vacuity theorem; contrast
`SymPowColimit.permAut_swap_ne_id_of_points`, which is a genuine non-vacuity statement
because it refutes an equality. -/
theorem tprod_const_mem_symTensorPowSubalgebra (a : A) :
    tprod R (fun _ : ι => a) ∈ symTensorPowSubalgebra R A := by
  intro σ
  simp

end Action

end PiTensorProduct

/-! ## §4. Milne's carrier as a quotient: instantiating `SymPowInvariants`

`Albanese/SymPowInvariants.lean` proved, for an *arbitrary* group acting on an arbitrary
commutative ring, that the invariants are the limit of the action diagram in `CommRingCat`
and hence a colimit in `CommRingCatᵒᵖ`. Its §4 listed the specialisation to Milne's ring as
open, because the action did not exist. It does now, so the specialisation is available, and
this section takes it.

The universe constraint is worth naming since it is what forces `Fin n` rather than a general
finite `ι`: `SymPowInvariants.actionDiagram` wants the group and the ring in the *same*
universe `u` as `CommRingCat.{u}`. `Equiv.Perm (Fin n)` lives in `Type 0`, so the
instantiation below fixes `R`, `A` in `Type 0` too. That is no loss for Milne: `S_n` is the
group he uses, and a curve chart's coordinate ring can be taken in `Type 0`… but it *is* a
restriction relative to §1–§3, which are universe-polymorphic. Lifting it would mean a
`ULift` of the group, and nothing here needs that. -/

namespace AlgebraicGeometry

open PiTensorProduct

variable (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (n : ℕ)

/-- **Milne's affine carrier is the limit of the `S_n`-action** — `SymPowInvariants`'
`fixedConeIsLimit` at the tensor-power action.

Combined with `symTensorPowSubalgebra_toSubring`, this says: `(A^{⊗ n})^{S_n}` is the limit
in `CommRingCat` of the `S_n`-action on `A^{⊗ n}`. -/
theorem hasLimit_actionDiagram_symTensorPow :
    letI := permMulSemiringAction R (ι := Fin n) A
    HasLimit (actionDiagram (Equiv.Perm (Fin n)) (⨂[R] _ : Fin n, A)) :=
  letI := permMulSemiringAction R (ι := Fin n) A
  hasLimit_actionDiagram _ _

/-- **Milne's affine carrier is a quotient** — the colimit form, in `CommRingCatᵒᵖ`.

Geometrically: `Spec ((A^{⊗ n})^{S_n})` is the quotient of `Spec (A^{⊗ n}) = (Spec A)^n` by
the permutation action, which is Milne III.3 Proposition 3.1's affine half *with its carrier
named*. What is still missing for the proposition itself is the gluing over a cover of the
curve (`Albanese/SymPowColimit.lean` §6) and the category bridge recorded in this file's
scope section — so this is the affine statement, not the proposition. -/
theorem hasColimit_actionDiagram_op_symTensorPow :
    letI := permMulSemiringAction R (ι := Fin n) A
    HasColimit (actionDiagram (Equiv.Perm (Fin n)) (⨂[R] _ : Fin n, A)).op :=
  letI := permMulSemiringAction R (ι := Fin n) A
  hasColimit_actionDiagram_op _ _

end AlgebraicGeometry


