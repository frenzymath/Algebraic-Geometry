/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.PicRepDatum
import AlgebraicJacobian.Picard.JacobianData

/-!
# Lightweight `PicRepDatum` to `JacobianData` handoff

This module is the challenge-facing DAT-G to DAT-J interface.  It deliberately imports no
Abel-surjectivity or Riemann--Roch modules: an eventual arbitrary-field Picard producer can
package its exact representation here without creating the import cycle through
`RiemannRoch.ChiCurve` and `Challenge`.

The only additional datum is quasi-compactness.  The representing object, universal
equivalence, locally-finite-type certificate, and induced group object are carried across
definitionally.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace PicRepDatum

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]

/-- A representation datum at the challenge field, together with quasi-compactness of its
representing object, is the pinned `JacobianData`.  All shared fields are definitionally
unchanged. -/
noncomputable def toJacobianData (d : PicRepDatum k k C) (hqc : QuasiCompact d.J.hom) :
    JacobianData C where
  J := d.J
  rep := d.rep
  locallyOfFiniteType := d.lft
  quasiCompact := hqc

@[simp]
lemma toJacobianData_J (d : PicRepDatum k k C) (hqc : QuasiCompact d.J.hom) :
    (d.toJacobianData hqc).J = d.J :=
  rfl

@[simp]
lemma toJacobianData_rep (d : PicRepDatum k k C) (hqc : QuasiCompact d.J.hom) :
    (d.toJacobianData hqc).rep = d.rep :=
  rfl

/-- The group-object structure survives the handoff definitionally. -/
@[simp]
lemma toJacobianData_grpObj (d : PicRepDatum k k C) (hqc : QuasiCompact d.J.hom) :
    (d.toJacobianData hqc).grpObj = d.grpObj :=
  rfl

/-- The universal properties of the packaged datum and the original datum agree. -/
@[simp]
lemma homEquiv_toJacobianData (d : PicRepDatum k k C) (hqc : QuasiCompact d.J.hom)
    {T : Over (Spec (.of k))} :
    (d.toJacobianData hqc).homEquiv (T := T) = d.homEquiv (T := T) :=
  rfl

end PicRepDatum

end AlgebraicGeometry
