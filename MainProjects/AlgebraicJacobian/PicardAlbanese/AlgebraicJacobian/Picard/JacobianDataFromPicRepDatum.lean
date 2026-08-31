/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.JacobianDataHandoff
import AlgebraicJacobian.Picard.JacobianDataAbelSurj

/-!
# The `PicRepDatum` handoff with quasi-compactness supplied by Abel lifts

`informal/w4-datj-worksheet.md` §1.1/§0.9 pins the interface DAT-J consumes from DAT-G as
**DJ-IN** = `PicRepDatum k k C`, and its §1.1 producer target reads

```
jacobianData C : JacobianData C where
  J := (datGDatum C).J ; rep := (datGDatum C).rep
  locallyOfFiniteType := (datGDatum C).lft ; quasiCompact := quasiCompact_jacobian C
```

with the note that *"every symbol on the RHS except `datGDatum` (DAT-G) and
`quasiCompact_jacobian` (DJ-1) is landed"* and that the `rep :=` line needs **no adapter**
because the two field types are definitionally equal (`Picard/PicRepDatum.lean`, the module's
defeq smoke test).

The lightweight packaging and its definitional compatibility lemmas live in
`Picard/JacobianDataHandoff.lean`.  Keeping them there prevents the eventual challenge-field
producer from importing the Abel-surjectivity and Riemann--Roch dependency cone.

The content is exactly the interface, so it is short by design — but it is not nothing:
writing it is what turns "DAT-G produces a datum over `k'`, and separately DAT-J wants one
over `k`" into a single arrow, and it is what makes the remaining DAT-J debt *visibly* two
statements (the DAT-G descent, and the quasi-compactness) rather than an unspecified
assembly.

## Main declarations

* `AlgebraicGeometry.PicRepDatum.toJacobianDataOfAbelLifts` — the same with quasi-compactness
  supplied in the shape the classical argument delivers it: per-point residue-field lifts of
  an Abel morphism out of `DivScheme g` (`Picard/JacobianDataAbelSurj.lean`).

## What this does NOT do

It produces no `PicRepDatum`.  That is DAT-G/DAT-G0 — the finite-Galois descent from a
finite separable stage, whose one avatar-less core is `Pic0PreservesFilteredBaseColimit`
(`Picard/PicRepColimitCompat.lean`), and it is divRep-gated.  Nor does it produce the
quasi-compactness or an Abel lift.  What it removes is the *assembly* step between them.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace PicRepDatum

/-! ## The handoff with quasi-compactness in its a-posteriori shape -/

section AbelLifts

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))] [IsIntegral X]
variable {A B : X.CurveDivisor} {g r₁ r₂ : ℕ}
variable {b₁ : Module.Basis (Fin r₁) k ↥(Scheme.divisorSections k B ⊤)}
variable {b₂ : Module.Basis (Fin r₂) k ↥(Scheme.divisorSections k (A + B) ⊤)}

/-- **DJ-IN composed with DJ-1**: the challenge-field datum plus an Abel morphism out of
`DivScheme g` admitting a residue-field lift at every point of `d.J.left` is a
`JacobianData C`.

This is the shape the whole DAT-J assembly actually has: DAT-G supplies the datum, and
quasi-compactness comes from the Abel image (w4-datj §2.2), never from the construction —
`JacobianData`'s atlas is infinite (critical-path §7.5).  So the two remaining inputs of
DAT-J are visible in this signature and nowhere else: a `PicRepDatum k k C`, and a lift. -/
noncomputable def toJacobianDataOfAbelLifts (d : PicRepDatum k k C)
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ d.J.left)
    (hlift : ∀ y : d.J.left, ∃ q : Spec (d.J.left.residueField y) ⟶
      DivScheme k A B g r₁ r₂ b₁ b₂,
      q ≫ abel = d.J.left.fromSpecResidueField y) :
    JacobianData C :=
  d.toJacobianData
    (quasiCompact_of_forall_residueField_lift_from_divScheme A B g r₁ r₂ b₁ b₂ d.J abel hlift)

@[simp]
lemma toJacobianDataOfAbelLifts_J (d : PicRepDatum k k C)
    (abel : DivScheme k A B g r₁ r₂ b₁ b₂ ⟶ d.J.left)
    (hlift : ∀ y : d.J.left, ∃ q : Spec (d.J.left.residueField y) ⟶
      DivScheme k A B g r₁ r₂ b₁ b₂,
      q ≫ abel = d.J.left.fromSpecResidueField y) :
    (d.toJacobianDataOfAbelLifts abel hlift).J = d.J :=
  rfl

end AbelLifts

end PicRepDatum

end AlgebraicGeometry
