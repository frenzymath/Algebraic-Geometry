/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Albanese.AlbaneseFromData
import AlgebraicJacobian.Albanese.AVSelfProduct
import AlgebraicJacobian.Albanese.AlbaneseUP

/-!
# The Albanese universal property of `Pic⁰_{C/k̄}`, at the Jacobian

`Albanese/AlbaneseFromData.lean` proves Milne Proposition III.6.1 over the
symmetric-power interface in an arbitrary cartesian monoidal category. This file
instantiates it at the object the challenge cares about: `J = Pic⁰_{C/k̄}` for a
smooth proper geometrically irreducible curve `C` over an algebraically closed field.

The point of the instantiation is that **every hypothesis of the general theorem is
discharged here except one**. Specifically:

* `IsCommMonObj (Pic0.jacobianScheme C)` and `IsCommMonObj A` — Milne §I.1 Corollary
  1.4, now available on the project's four-instance package
  (`isCommMonObj_of_isProper_smooth_of_package`, `Albanese/AVSelfProduct.lean`).
* **pointed rigidity** for `Pic⁰ ⟶ A` — Milne §I.1 Corollary 1.2, likewise
  (`isMonHom_of_pointed`). This is the `hom` input, and it rests on the sorry-free
  rigidity chain of `RigidityLemma.lean`.
* the connector in both directions, and the assembly — proved in
  `Albanese/AlbaneseFromData.lean`.

What is **not** discharged, and is the entire remaining content of this leg:

> `SymPowData C (genus C)` — the `g`-th symmetric power of the curve, with its
> symmetrisation projection and universal property,

together with the cycle map presented as the symmetrisation of a pointed Abel–Jacobi
map (`hf`, `haj0`) and the descent datum, which `Albanese/AlbaneseFromData.lean` §2
reduces to a morphism on a dense open (Milne III.5.1(a) birationality).

## Main result

* `Pic0.albanese_universal_property_of_symPowData` — the Albanese universal property
  of `Pic⁰_{C/k̄}`, with the symmetric power as an explicit argument. Axiom-clean
  apart from what `Pic0.jacobianScheme` itself carries (see below).

## An honest note on `sorryAx`

`Pic0.jacobianScheme C` is built from `Pic0.bundle`, which routes through the Picard
representability seam; at a *synthesis site* that seam still reports `sorryAx`
(the five obligations named on the AJC team thread, none of them in this leg). So this
theorem is **not** a closed result about the actual Jacobian, and must not be reported
as one. What it does establish is sharp and worth stating precisely:

> the Albanese *argument* is complete. Given the symmetric power, Milne III.6.1 holds
> for `Pic⁰_{C/k̄}` with no further input from this leg.

That is a different claim from `albanese_universal_property` in
`Albanese/AlbaneseUP.lean`, which quantifies over a `sorry`-bodied `abelJacobi` and a
`sorry`-bodied `SymmetricPower` and therefore asserts nothing about either.

## References

Milne, *Abelian Varieties*, §III.6 Proposition 6.1, p. 104; §I.1 Corollaries 1.2 and
1.4. Blueprint `thm:albanese_universal_property`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

namespace Pic0

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

variable (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]

/-- **The Albanese universal property of `Pic⁰_{C/k̄}` — Milne Proposition III.6.1,
with the symmetric power supplied as data.**

Let `C` be a smooth proper geometrically irreducible curve over an algebraically
closed field `k̄`, let `A` be an abelian variety over `k̄`, and let `φ : C ⟶ A` be
*pointed* at `P₀`. Suppose given

* `D : SymPowData C (genus C)` — the `g`-th symmetric power with its symmetrisation
  projection `π` and universal property, and the symmetry of `π` itself (`hproj`);
* `f : Sym^g C ⟶ Pic⁰` presented as the symmetrisation of a pointed Abel–Jacobi map
  `aj` (`hf : π ≫ f = aj(P₁) + ⋯ + aj(P_g)`, `haj0 : aj(P₀) = η_J`);
* the descent datum `hdesc` — a unique `ψ` with `Sym^g φ = f ≫ ψ` (Milne's step 2,
  reduced by `Albanese/AlbaneseFromData.lean` §2 to a morphism on a dense open of
  `Pic⁰`).

Then there is a **unique** `ψ : Pic⁰_{C/k̄} ⟶ A` with `φ = aj ≫ ψ`.

Every other ingredient of Milne's proof is discharged in the body: commutativity of
both group objects and pointed rigidity for `Pic⁰ ⟶ A` (Milne I.1.4 and I.1.2, via
`Albanese/AVSelfProduct.lean`), and the connector in both directions
(`Albanese/AlbaneseFromData.lean`). See the module header for why this is a statement
about the Albanese *argument* rather than a closed result about the Jacobian. -/
theorem albanese_universal_property_of_symPowData
    (D : SymPowData C (genus C))
    (hproj : ∀ σ : Equiv.Perm (Fin (genus C)),
      permAut C σ ≫ D.proj = D.proj)
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) (i₀ : Fin (genus C))
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A])
    (aj : C ⟶ jacobianScheme C) (f : D.carrier ⟶ jacobianScheme C)
    (hf : letI := jacobianScheme_grpObj C
      letI : IsCommMonObj (jacobianScheme C) := by
        haveI := jacobianScheme_isProper C
        haveI := jacobianScheme_smooth C
        haveI := jacobianScheme_geomIrred C
        exact isCommMonObj_of_isProper_smooth_of_package _
      D.proj ≫ f = powSum (genus C) aj)
    (haj0 : letI := jacobianScheme_grpObj C; P0 ≫ aj = η[jacobianScheme C])
    (hdesc : letI := jacobianScheme_grpObj C
      letI : IsCommMonObj A := isCommMonObj_of_isProper_smooth_of_package A
      ∃! ψ : jacobianScheme C ⟶ A, D.symAVMap φ = f ≫ ψ) :
    ∃! ψ : jacobianScheme C ⟶ A, φ = aj ≫ ψ := by
  letI := jacobianScheme_grpObj C
  haveI := jacobianScheme_isProper C
  haveI := jacobianScheme_smooth C
  haveI := jacobianScheme_geomIrred C
  -- Milne I.1.4 for both group objects (`Albanese/AVSelfProduct.lean`).
  letI : IsCommMonObj (jacobianScheme C) :=
    isCommMonObj_of_isProper_smooth_of_package _
  letI : IsCommMonObj A := isCommMonObj_of_isProper_smooth_of_package A
  -- Milne I.1.2: a pointed morphism `Pic⁰ ⟶ A` is a homomorphism.
  exact exists_unique_albanese_factorisation D f P0 i₀ hproj aj hf haj0 φ hφ
    (fun ψ hψ => isMonHom_of_pointed ψ hψ) hdesc

end Pic0

/-! ## The attribution of `sorryAx`, made checkable

`Pic0.albanese_universal_property_of_symPowData` reports `sorryAx`, and it would be
easy — and wrong — to read that as a gap in the Albanese argument. The theorem below
is the *same statement with `Pic⁰_{C/k̄}` replaced by an arbitrary abelian variety
`J`*, and it is **axiom-clean**:

```
#print axioms albanese_universal_property_of_symPowData_generic
  -- [propext, Classical.choice, Quot.sound]
#print axioms Pic0.albanese_universal_property_of_symPowData
  -- [propext, sorryAx, Classical.choice, Quot.sound]
```

The two differ only in the target group object. So the entire `sorryAx` residue of
the specialised form is `Pic0.jacobianScheme` — i.e. the Picard representability seam
upstream of this leg — and **none** of it is the Albanese argument. This is the
measurement that turns "the argument is complete" from a claim in a docstring into
something a later session can re-run.

It also drops the curve hypotheses: nothing in Milne's III.6.1 argument, once the
symmetric power is given, uses that `C` is a curve. The genus enters only as the
number `g` of factors. -/

/-- **The Albanese universal property with an arbitrary abelian variety as target.**

Milne Proposition III.6.1 in its widest honest form: for *any* object `C`, any `g`,
any symmetric-power datum `SymPowData C g`, and any two abelian varieties `J`, `A`
over `k̄`, a pointed `φ : C ⟶ A` factors uniquely through a pointed `aj : C ⟶ J` whose
symmetrisation is `f`, given the descent datum.

Axiom-clean. Its role is twofold: it is the reusable statement (nothing about curves
or the Jacobian is needed), and comparing its axiom set with that of
`Pic0.albanese_universal_property_of_symPowData` attributes the latter's `sorryAx`
entirely to the Picard seam. See the section note above. -/
theorem albanese_universal_property_of_symPowData_generic
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) (g : ℕ)
    (D : SymPowData C g)
    (hproj : ∀ σ : Equiv.Perm (Fin g), permAut C σ ≫ D.proj = D.proj)
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) (i₀ : Fin g)
    {J A : Over (Spec (.of kbar))}
    [GrpObj J] [IsProper J.hom] [Smooth J.hom] [GeometricallyIrreducible J.hom]
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (hφ : P0 ≫ φ = η[A])
    (aj : C ⟶ J) (f : D.carrier ⟶ J)
    (hf : letI : IsCommMonObj J := isCommMonObj_of_isProper_smooth_of_package J
      D.proj ≫ f = powSum g aj)
    (haj0 : P0 ≫ aj = η[J])
    (hdesc : letI : IsCommMonObj A := isCommMonObj_of_isProper_smooth_of_package A
      ∃! ψ : J ⟶ A, D.symAVMap φ = f ≫ ψ) :
    ∃! ψ : J ⟶ A, φ = aj ≫ ψ := by
  letI : IsCommMonObj J := isCommMonObj_of_isProper_smooth_of_package J
  letI : IsCommMonObj A := isCommMonObj_of_isProper_smooth_of_package A
  exact exists_unique_albanese_factorisation D f P0 i₀ hproj aj hf haj0 φ hφ
    (fun ψ hψ => isMonHom_of_pointed ψ hψ) hdesc

end AlgebraicGeometry
