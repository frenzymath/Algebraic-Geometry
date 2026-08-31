/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import Mathlib
import AlgebraicJacobian.Jacobian

/-!
# The Abel-Jacobi map

The Abel-Jacobi map from a smooth, proper curve to its Jacobian, and the universal property
of the Jacobian as the Albanese variety.

Since `Jacobian C` is by definition `(jacobianWitness C).J`, every declaration below is a
projection of the Albanese universal property carried by the witness field
`(jacobianWitness C).isAlbaneseFor P : IsAlbanese C P (jacobianWitness C).J`.

## Main results

* `Jacobian.ofCurve`: the Abel-Jacobi map `C ⟶ Jacobian C` attached to a `k`-rational point
  `P` of `C`.
* `Jacobian.comp_ofCurve`: the Abel-Jacobi map sends `P` to the neutral element of
  `Jacobian C`.
* `Jacobian.exists_unique_ofCurve_comp`: a morphism `f : C ⟶ A` to an abelian variety with
  `P ≫ f = η[A]` factors uniquely through the Abel-Jacobi map.

## Remaining obligations

The genus-0 rigidity input (classical rigidity `Hom(ℙ¹, A) = A(k)`) is not proved here: it is
part of the existence claim `nonempty_jacobianWitness` in `AlgebraicJacobian.Jacobian`, which is
still open.  The `isAlbaneseFor` field of a witness must verify the Albanese property for
genus-0 curves too, which is exactly that rigidity content.

## References

Source: [Mumford], *Abelian Varieties*, §4 (rigidity).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k] (C : Over (Spec (.of k)))
  [SmoothOfRelativeDimension 1 C.hom]
  [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

namespace Jacobian

variable {C} in
-- data
/-- The Abel-Jacobi map from a smooth, proper curve to its Jacobian associated
to a `k`-rational point of `C`. Projects the Albanese universal morphism carried
by the witness `(jacobianWitness C).isAlbaneseFor P`. -/
noncomputable def ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) : C ⟶ Jacobian C := by
  letI := (jacobianWitness C).grpObj
  letI := (jacobianWitness C).proper
  letI := (jacobianWitness C).smooth
  letI := (jacobianWitness C).geomIrred
  exact ((jacobianWitness C).isAlbaneseFor P).ofCurve

variable {C} in
/-- The Abel-Jacobi map sends the `k`-rational point `P` to `0`, where `0` (denoted by `η` below) is
the neutral element of the group scheme `Jacobian C`. Projects the pointed-property
of the Albanese witness `(jacobianWitness C).isAlbaneseFor P`. -/
lemma comp_ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ofCurve P = η[Jacobian C] := by
  letI := (jacobianWitness C).grpObj
  letI := (jacobianWitness C).proper
  letI := (jacobianWitness C).smooth
  letI := (jacobianWitness C).geomIrred
  exact ((jacobianWitness C).isAlbaneseFor P).comp_ofCurve

variable {C} in
/--
The universal property of the Jacobian variety: For any abelian variety `A`,
any morphism `f : C ⟶ A` such that `f(P) = 0` factors uniquely through the
Jacobian of `C`.
In other words, `Jacobian C` is the Albanese variety of `C`.

The existence-and-uniqueness data is projected unconditionally from the witness
`(jacobianWitness C).isAlbaneseFor P`. The genus-0 rigidity content (`Hom(ℙ¹, A) = A(k)`,
Mumford §4) is absorbed into the deferred existence claim `nonempty_jacobianWitness`,
since the witness must verify the Albanese property for genus-0 curves too.
-/
theorem exists_unique_ofCurve_comp (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : Jacobian C ⟶ A), f = ofCurve P ≫ g := by
  letI := (jacobianWitness C).grpObj
  letI := (jacobianWitness C).proper
  letI := (jacobianWitness C).smooth
  letI := (jacobianWitness C).geomIrred
  exact ((jacobianWitness C).isAlbaneseFor P).exists_unique_ofCurve_comp f hf

end Jacobian

end AlgebraicGeometry
