/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.AVCommutative
import AlgebraicJacobian.Albanese.CodimOneExtension

/-!
# The self-product `A ⊗ A` of an abelian variety is again a variety

`Albanese/AVCommutative.lean` proves that an abelian variety over an algebraically
closed field is commutative (Milne §I.1 Corollary 1.4), but its statement carries
three hypotheses about the **self-product**:

`[GeometricallyIrreducible (A ⊗ A).hom]`, `[LocallyOfFiniteType (A ⊗ A).hom]`,
`[IsReduced (A ⊗ A).left]`.

These were left as hypotheses because typeclass synthesis cannot see through the
monoidal structure on `Over (Spec k̄)`: `A ⊗ A` is built from `Limits.pullback`, and
`(A ⊗ A).hom` is *reducibly* `pullback.fst A.hom A.hom ≫ A.hom`, but nothing keyed
on the tensor notation. So `isCommMonObj_of_isProper_smooth` could not be applied to
an abelian variety presented only by the project's four-instance package — and
`MonObj.powSum`, which needs `IsCommMonObj`, was unavailable in practice.

This file closes that. All three hypotheses are **theorems**, not assumptions:

* `smooth_tensorObj_self` — rewrite along `Over.tensorObj_hom` and the composite
  `pullback.fst ≫ A.hom` is smooth (base change of a smooth morphism, then
  composition), so mathlib's instances apply once the goal is in pullback form.
* `locallyOfFiniteType_tensorObj_self`, `geometricallyIrreducible_tensorObj_self` —
  the same rewrite; geometric irreducibility composes
  (`GeometricallyIrreducible.comp`).
* `isReduced_tensorObj_self_left` — `A ⊗ A` is smooth over `k̄` by the first item, and
  a smooth scheme over an algebraically closed field is reduced
  (`Scheme.isReduced_of_smooth_of_isAlgClosed`, already in the project).

## The payoff

`isCommMonObj_of_isProper_smooth_of_package` applies Milne I.1.4 to an abelian
variety carrying **only** the project's standard package
(`GrpObj`, `IsProper`, `Smooth`, `GeometricallyIrreducible`). That is the form every
call site has, so commutativity — and with it `MonObj.powSum` and the whole
symmetrisation step — is now available without threading side conditions.

Likewise `isMonHom_of_pointed` restates Milne §I.1 Corollary 1.2 on the standard
package: a *pointed* morphism of abelian varieties is a homomorphism. This is the
`hom` input of `exists_unique_albanese_factorisation`
(`Albanese/AlbaneseFromData.lean`).

## The lesson, recorded because it recurs

The obstruction was never mathematical; it was instance **keying**. A goal stated in
`⊗` notation and the same goal stated in `pullback` form are definitionally equal and
yet only the second is solvable by synthesis. When an abelian-variety side condition
on `A ⊗ A` looks like missing infrastructure, try `rw [Over.tensorObj_hom]` or
`rw [Over.tensorObj_left]` first.

## References

Milne, *Abelian Varieties*, §I.1 Corollary 1.2 and Corollary 1.4. Blueprint
`chap:AbelianVarietyRigidity`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

/-! ## §1. The three side conditions on `A ⊗ A`

Each is the corresponding mathlib instance for `pullback.fst A.hom A.hom ≫ A.hom`,
reached by rewriting the tensor notation into pullback form. -/

omit [IsAlgClosed kbar] in
/-- **The self-product of a smooth `k̄`-scheme is smooth over `k̄`.**
`(A ⊗ A).hom` is `pullback.fst A.hom A.hom ≫ A.hom`; the first factor is a base
change of the smooth `A.hom` and smoothness is stable under composition. -/
theorem smooth_tensorObj_self (A : Over (Spec (.of kbar))) [Smooth A.hom] :
    Smooth (A ⊗ A).hom := by
  rw [Over.tensorObj_hom]
  exact inferInstanceAs (Smooth (pullback.fst A.hom A.hom ≫ A.hom))

omit [IsAlgClosed kbar] in
/-- **The self-product is locally of finite type over `k̄`.** Same rewrite; smooth
morphisms are locally of finite type and the property composes. -/
theorem locallyOfFiniteType_tensorObj_self (A : Over (Spec (.of kbar)))
    [Smooth A.hom] : LocallyOfFiniteType (A ⊗ A).hom := by
  rw [Over.tensorObj_hom]
  exact inferInstanceAs (LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom))

omit [IsAlgClosed kbar] in
/-- **The self-product is geometrically irreducible over `k̄`.** The projection
`pullback.fst A.hom A.hom` is a base change of the geometrically irreducible `A.hom`,
and geometric irreducibility composes (`GeometricallyIrreducible.comp`). -/
theorem geometricallyIrreducible_tensorObj_self (A : Over (Spec (.of kbar)))
    [GeometricallyIrreducible A.hom] : GeometricallyIrreducible (A ⊗ A).hom := by
  rw [Over.tensorObj_hom]
  exact GeometricallyIrreducible.comp (pullback.fst A.hom A.hom) A.hom

/-- **The underlying scheme of the self-product is reduced.** It is smooth over `k̄`
by `smooth_tensorObj_self`, and a scheme smooth over an algebraically closed field is
reduced (`Scheme.isReduced_of_smooth_of_isAlgClosed`). -/
theorem isReduced_tensorObj_self_left (A : Over (Spec (.of kbar))) [Smooth A.hom] :
    IsReduced (A ⊗ A).left := by
  haveI := smooth_tensorObj_self A
  exact Scheme.isReduced_of_smooth_of_isAlgClosed (A ⊗ A)

/-! ## §2. Milne I.1.2 and I.1.4 on the project's standard package

With §1 the two rigidity corollaries apply to an abelian variety carrying only
`[GrpObj] [IsProper] [Smooth] [GeometricallyIrreducible]`. -/

/-- **Milne §I.1 Corollary 1.4 on the standard package — an abelian variety is
commutative.**

Same statement as `isCommMonObj_of_isProper_smooth`, but with the three self-product
hypotheses discharged by §1, so it applies to any `A` carrying the project's
four-instance abelian-variety package.

This is what makes `MonObj.powSum` (`Albanese/GrpObjFoldSum.lean`) usable at an
actual abelian variety, and hence the symmetrisation step of Milne III.6.1
available. -/
theorem isCommMonObj_of_isProper_smooth_of_package (A : Over (Spec (.of kbar)))
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom] :
    IsCommMonObj A := by
  haveI := geometricallyIrreducible_tensorObj_self A
  haveI := locallyOfFiniteType_tensorObj_self A
  haveI := isReduced_tensorObj_self_left A
  exact isCommMonObj_of_isProper_smooth

/-- **Milne §I.1 Corollary 1.2 on the standard package — a pointed morphism of
abelian varieties is a homomorphism.**

`av_regularMap_isHom_of_zero` with the three self-product hypotheses discharged. This
is exactly the `hom` input of
`CategoryTheory.exists_unique_albanese_factorisation`
(`Albanese/AlbaneseFromData.lean`): pointed rigidity for the Jacobian. -/
theorem isMonHom_of_pointed {A B : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    [GrpObj B] [IsProper B.hom]
    (α : A ⟶ B) (hα : η[A] ≫ α = η[B]) : IsMonHom α := by
  haveI := geometricallyIrreducible_tensorObj_self A
  haveI := locallyOfFiniteType_tensorObj_self A
  haveI := isReduced_tensorObj_self_left A
  exact av_regularMap_isHom_of_zero α hα

end AlgebraicGeometry
