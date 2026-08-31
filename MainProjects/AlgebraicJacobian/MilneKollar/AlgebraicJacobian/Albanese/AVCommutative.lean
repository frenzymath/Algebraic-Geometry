/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.RigidityLemma

/-!
# An abelian variety is commutative (Milne §I.1 Corollary 1.4)

The group law of an abelian variety is commutative. This is Milne, *Abelian
Varieties*, §I.1 Corollary 1.4, and it is a consequence of the Rigidity Lemma
via Corollary 1.2 (`av_regularMap_isHom_of_zero`, `RigidityLemma.lean`).

## The argument

The inversion morphism `inv : A ⟶ A` of a group object is *pointed*: it sends the
identity to the identity (`GrpObj.one_inv`). By Milne Corollary 1.2 — every
pointed regular map between abelian varieties is a homomorphism — inversion is
therefore a **homomorphism** of group objects.

A group in which `x ↦ x⁻¹` is a homomorphism is commutative: from
`(xy)⁻¹ = x⁻¹y⁻¹` and `(xy)⁻¹ = y⁻¹x⁻¹` one gets `x⁻¹y⁻¹ = y⁻¹x⁻¹`, and inverting
gives `yx = xy`. Applying this in each hom-group `Hom(X, A)` — which mathlib
already knows is a `Group` when `A` is a group object — and then instantiating at
`X := A ⊗ A` with the two projections yields the object-level statement
`(β_ A A).hom ≫ μ = μ`, i.e. `IsCommMonObj A`.

## Why this file exists

`IsCommMonObj A` is precisely the instance that
`Albanese/GrpObjFoldSum.lean`'s `MonObj.powSum` requires: the `g`-fold sum
`(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` is formed in the *commutative* monoid
`(C^g ⟶ A)`, and its `S_g`-symmetry (`MonObj.powSum_perm`) is exactly the
commutativity of `A`'s group law. Before this file, the project's
abelian-variety hypothesis package (`[GrpObj A] [IsProper A.hom] [Smooth A.hom]
[GeometricallyIrreducible A.hom]`) did **not** yield `IsCommMonObj A` by
synthesis, so `powSum` could not be instantiated at an actual abelian variety.
`isCommMonObj_of_isProper_smooth` closes that gap, making the symmetrisation step
of Milne III.6.1 applicable to its intended target.

## Main results

* `AlgebraicGeometry.isMonHom_grpObj_inv` — inversion on an abelian variety is a
  homomorphism (Milne I.1.2 applied to the pointed map `inv`).
* `CategoryTheory.MonObj.mul_comm_hom_of_isMonHom_inv` — the group-theoretic step,
  in any cartesian monoidal category: if inversion is a homomorphism then every
  hom-group `Hom(X, A)` is commutative.
* `CategoryTheory.IsCommMonObj.of_hom_mul_comm` — commutativity of all hom-groups
  upgrades to `IsCommMonObj`.
* `AlgebraicGeometry.isCommMonObj_of_isProper_smooth` — **Milne I.1.4**: an
  abelian variety is a commutative group object.

## References

Milne, *Abelian Varieties*, §I.1 Corollary 1.4 (and Corollary 1.2), pp. 5–7
(`references/abelian-varieties.pdf`). Blueprint: `chap:AbelianVarietyRigidity`.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory.MonObj

variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K]

/-- **If inversion is a homomorphism, every hom-group is commutative.**

Purely group-theoretic, in any cartesian monoidal category. Postcomposition with
`GrpObj.inv` is inversion in the hom-group `Hom(X, A)` (`Hom.inv_def`), so the
hypothesis says `(u * v)⁻¹ = u⁻¹ * v⁻¹` there. Since always
`(u * v)⁻¹ = v⁻¹ * u⁻¹`, inverting both sides of `u⁻¹ * v⁻¹ = v⁻¹ * u⁻¹` gives
commutativity. -/
theorem mul_comm_hom_of_isMonHom_inv {A : K} [GrpObj A]
    (hinv : IsMonHom (GrpObj.inv (X := A))) (X : K) (f g : X ⟶ A) :
    f * g = g * f := by
  have key : ∀ u v : X ⟶ A, (u * v) ≫ GrpObj.inv (X := A)
      = (u ≫ GrpObj.inv (X := A)) * (v ≫ GrpObj.inv (X := A)) := by
    intro u v
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hinv.mul_hom]
    simp [lift_map_assoc]
  have h1 := key f g
  rw [← Hom.inv_def, ← Hom.inv_def, ← Hom.inv_def] at h1
  -- `h1 : (f * g)⁻¹ = f⁻¹ * g⁻¹`; invert, using `(f * g)⁻¹ = g⁻¹ * f⁻¹`.
  have h2 : ((f * g)⁻¹)⁻¹ = (f⁻¹ * g⁻¹)⁻¹ := by rw [h1]
  simpa using h2

end CategoryTheory.MonObj

namespace CategoryTheory.IsCommMonObj

variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K] [BraidedCategory K]

/-- **Commutativity of all hom-groups upgrades to `IsCommMonObj`.** Instantiate
hom-commutativity at `X := A ⊗ A` with the two projections: `fst * snd` is
`lift fst snd ≫ μ = μ`, while `snd * fst` is `lift snd fst ≫ μ`, and in a
cartesian monoidal category `lift snd fst` *is* the braiding. -/
theorem of_hom_mul_comm {A : K} [MonObj A]
    (hcomm : ∀ (X : K) (f g : X ⟶ A), f * g = g * f) : IsCommMonObj A := by
  constructor
  have h := hcomm (A ⊗ A) (fst A A) (snd A A)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
  have hb : (β_ A A).hom = lift (snd A A) (fst A A) := by
    apply hom_ext <;> simp
  rw [hb, ← h]

end CategoryTheory.IsCommMonObj

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

/-- **Inversion on an abelian variety is a homomorphism.** The inversion morphism
is pointed (`GrpObj.one_inv` : `η ≫ inv = η`), so Milne §I.1 Corollary 1.2
(`av_regularMap_isHom_of_zero`, a consequence of the Rigidity Lemma) applies. -/
theorem isMonHom_grpObj_inv {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    [GeometricallyIrreducible (A ⊗ A).hom] [LocallyOfFiniteType (A ⊗ A).hom]
    [IsReduced (A ⊗ A).left] :
    IsMonHom (GrpObj.inv (X := A)) :=
  av_regularMap_isHom_of_zero _ GrpObj.one_inv

/-- **Milne §I.1 Corollary 1.4 — an abelian variety is commutative.**

The group law of an abelian variety over an algebraically closed field is
commutative: `A` is a commutative group object, `IsCommMonObj A`.

The proof is Milne's: inversion is pointed, hence a homomorphism by Corollary 1.2
(`isMonHom_grpObj_inv`, resting on the Rigidity Lemma); a group whose inversion is
a homomorphism is commutative (`mul_comm_hom_of_isMonHom_inv`); and commutativity
of every hom-group is `IsCommMonObj` (`IsCommMonObj.of_hom_mul_comm`).

This supplies the instance that `MonObj.powSum` (`Albanese/GrpObjFoldSum.lean`)
needs, so the `g`-fold sum `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` and its
`S_g`-symmetry become available at an actual abelian variety — the symmetrisation
step of Milne III.6 Proposition 6.1.

Deliberately **not** an `instance`: the three `(A ⊗ A)`-side hypotheses are not
derived by synthesis from the abelian-variety package here, so consumers thread it
explicitly (`letI := isCommMonObj_of_isProper_smooth (A := A)`), matching the
convention used for `Pic0.jacobianScheme_grpObj` in `Albanese/AlbaneseUP.lean`. -/
theorem isCommMonObj_of_isProper_smooth {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    [GeometricallyIrreducible (A ⊗ A).hom] [LocallyOfFiniteType (A ⊗ A).hom]
    [IsReduced (A ⊗ A).left] :
    IsCommMonObj A :=
  IsCommMonObj.of_hom_mul_comm
    (MonObj.mul_comm_hom_of_isMonHom_inv isMonHom_grpObj_inv)

end AlgebraicGeometry
