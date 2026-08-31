/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianData
import AlgebraicJacobian.Picard.AbelElement

/-!
# The datum-level Abel–Jacobi map and its pointing law (Wave 6, `ofCurve`/`comp_ofCurve`)

`Picard/AbelElement.lean` builds the Abel element `abelElement C P : pic0Subgroup C C` and
proves the pointing law `abelElement_map_point`.  `Picard/JacobianData.lean` pins the
representability datum with its universal property `homEquiv : (T ⟶ d.J) ≃ pic0Subgroup C T`.
This file is the one-line bridge between them that the frozen Wave-6 gates consume:

* `AlgebraicGeometry.JacobianData.ofCurve` — the Abel–Jacobi map `C ⟶ d.J` of a rational
  point, `d.homEquiv.symm (abelElement C P)`.  The frozen `Jacobian.ofCurve`
  (`Challenge.lean:125`) is `(jacobianData C).ofCurve P` on the nose, since
  `Jacobian C := (jacobianData C).J`.
* `AlgebraicGeometry.JacobianData.homEquiv_one` — the universal property sends the unit
  section to the trivial class.  This is *not* free: `η[d.J]` is `MonObj.one` of
  `GrpObj.ofRepresentableBy`, which mathlib defines as `α.homEquiv'.symm 1`; the content
  is that `RepresentableBy.homEquiv'` (`ConcreteCategory/Representable.lean`) is
  `homEquiv` itself, so the two cancel.
* `AlgebraicGeometry.JacobianData.comp_ofCurve` — **the pointing law**
  `P ≫ d.ofCurve P = η[d.J]`, the datum-level avatar of the frozen
  `Jacobian.comp_ofCurve` (`Challenge.lean:130`).  Proved by injectivity of `homEquiv`,
  its naturality `homEquiv_comp` against `pic0Map`, and `abelElement_map_point`.

Nothing here assumes a producer for `jacobianData`; everything is stated for an arbitrary
`d : JacobianData C`, in the section-variable discipline `JacobianData.lean` fixes.  The
universal-property half of Wave 6 (`exists_unique_ofCurve_comp`, `Challenge.lean:141`) is
NOT addressed here and has no avatar anywhere.

## The coupling the frozen discharge depends on

`comp_ofCurve` transfers to `Challenge.lean:130` only if the frozen `Jacobian.instGrpObj`
is discharged **as** `(jacobianData C).grpObj`.  If DAT-J ever supplies a different `GrpObj
(Jacobian C)` instance, `η[Jacobian C]` there is a different unit and this avatar does not
apply.  That is a constraint on DAT-J, recorded here because this is where it bites.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace JacobianData

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]

/-- **The datum-level Abel–Jacobi map** (design §4.6; the frozen `Jacobian.ofCurve`,
`Challenge.lean:125`): the morphism `C ⟶ d.J` classifying the Abel element of the
rational point `P`.  Already used unnamed at
`Picard/JacobianDataBaseChangeAbel.lean:115`; naming it is what makes the frozen gate a
one-liner. -/
noncomputable def ofCurve (d : JacobianData C) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    C ⟶ d.J :=
  d.homEquiv.symm (abelElement C P)

@[simp]
theorem homEquiv_ofCurve (d : JacobianData C) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    d.homEquiv (d.ofCurve P) = abelElement C P :=
  d.homEquiv.apply_symm_apply _

/-- **The universal property sends the unit section to the trivial class**: the group
structure `d.grpObj` is `GrpObj.ofRepresentableBy`, whose `one` is by definition
`d.rep.homEquiv'.symm 1`, and `RepresentableBy.homEquiv'` IS `homEquiv` — so the two
cancel by `Equiv.apply_symm_apply`. -/
theorem homEquiv_one (d : JacobianData C) :
    letI := d.grpObj
    d.homEquiv (η[d.J]) = 1 :=
  d.homEquiv.apply_symm_apply 1

/-- **The pointing law** (the frozen `Jacobian.comp_ofCurve`, `Challenge.lean:130`): the
Abel–Jacobi map of `P` sends `P` itself to the neutral element of the group scheme
`d.J`.  Injectivity of the universal property reduces it to the naturality square
`homEquiv (P ≫ f) = pic0Map C P (homEquiv f)` and the landed pointing law
`abelElement_map_point`. -/
theorem comp_ofCurve (d : JacobianData C) (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    letI := d.grpObj
    P ≫ d.ofCurve P = η[d.J] := by
  letI := d.grpObj
  refine d.homEquiv.injective ?_
  rw [d.homEquiv_comp P (d.ofCurve P), homEquiv_ofCurve, homEquiv_one]
  exact abelElement_map_point P

end JacobianData

end AlgebraicGeometry
