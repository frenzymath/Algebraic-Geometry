/-
Copyright (c) 2026 The AlgebraicJacobian Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
import AlgebraicJacobian.Picard.EffectivityClose

/-!
# The (C2) effectivity close over a ring test: the module-finite-cover core

`PicEtAff.unit_surjective_of_section` (`EffectivityClose.lean`) proves the (C2)
surjectivity of the étale plus-construction unit over a **field** test `K`
admitting a curve point.  Reading its proof, the *only* field-specific step is the
refinement of the representing cover to a finite separable field extension
(`Algebra.EtaleCover.exists_finiteSeparableField_algHom`, field cofinality); it is
used solely to obtain `[Module.Finite K F.Carrier]` so the (C2) effectivity
theorem `Over.exists_cechPic_map_whiskerLeft_eq` applies.  Everything after that —
the rigidification keystone (`relPic.exists_isRigidified_rep`,
`Over.IsRigidified.cechPicMap_doubleInl_eq_doubleInr`), the effectivity descent,
and the `mk`-calculus close (`PicEtAff.unit_eq_mk`) — is already stated over an
arbitrary commutative-ring test with a section `σ`.

This file isolates that ring-general core:

* `PicEtAff.mk_mem_range_unit_of_moduleFinite` — over a ring test `A` admitting a
  curve point `σ`, a plus class **represented on a module-finite étale cover** is
  in the range of the unit: it comes from an honest relative Picard class.  This
  is the (C2) effectivity theorem repackaged at the plus-class level, with the
  cover kept general (module-finite, not necessarily a field extension).

## What this does *not* do, and what it isolates

It does **not** prove ring-level surjectivity of the unit.  Surjectivity over `A`
is equivalent to: *every* plus class of `PicEtAff C A` is represented on **some**
module-finite étale cover.  That equivalence is not a reduction — the reverse
direction is free, because `PicEtAff.unit_eq_mk` represents any in-range class on
the trivial cover `Algebra.EtaleCover.self A`, which is module-finite.  So a
"surjectivity from module-finite-cover representatives" wrapper would merely
re-spell surjectivity, not weaken it, and is deliberately **not** stated here.

The genuine open obligation the field proof discharges by cofinality, and which
this file does not, is therefore: *refine an arbitrary étale cover of `Spec A`
representing a given plus class to a module-finite one* — false for a general
étale cover of a general ring (see the moving lemma's counterexample,
`EffectivityMoving.lean`), so it must be supplied by the specific curve/base at
hand (e.g. the explicit finite cover of a concrete `Pic` computation).
`mk_mem_range_unit_of_moduleFinite` is the interface such a producer plugs into.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
  TopologicalSpace CategoryTheory.PresheafOfGroups

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable (C : Over (Spec (.of k)))
variable [IsProper C.hom] [GeometricallyIrreducible C.hom] [GeometricallyReduced C.hom]
variable {A : Type u} [CommRing A] [Algebra k A]

noncomputable section

/-- **The (C2) effectivity close for a module-finite cover over a ring test.**

Over a commutative-ring test `A` admitting a curve point `σ : overSpec k A ⟶ C`, a
plus class of `PicEtAff C A` that is represented on a **module-finite** étale cover
`E` of `Spec A` (by a descent class `x`) is in the range of the plus-construction
unit: it equals `PicEtAff.unit C A z` for an honest relative Picard class
`z : relPic C (overSpec k A)`.

This is the ring-general heart of `PicEtAff.unit_surjective_of_section`: the same
rigidification + (C2) descent + `mk`-calculus, with the field-cofinality
refinement stripped away and the module-finiteness of the cover taken as a
hypothesis rather than manufactured from a field extension. -/
theorem PicEtAff.mk_mem_range_unit_of_moduleFinite
    (σ : overSpec k A ⟶ C) (E : Algebra.EtaleCover A) [Module.Finite A E.Carrier]
    (x : descentClasses C E) :
    ∃ z : relPic C (overSpec k A), PicEtAff.unit C A z = PicEtAff.mk C E x := by
  -- a rigidified representative of the descent class over the cover (G1)
  obtain ⟨Lc, hrig, hLcrep⟩ := relPic.exists_isRigidified_rep
    (Over.overSpecMap ((Algebra.ofId A E.Carrier).restrictScalars k) ≫ σ)
    (x : relPic C (overSpec k E.Carrier))
  have hmem : relPicMk C (overSpec k E.Carrier) Lc ∈ descentClasses C E := by
    rw [hLcrep]
    exact x.2
  -- the on-the-nose descent equation (the rigidified transport keystone)
  have hdesc0 := Over.IsRigidified.cechPicMap_doubleInl_eq_doubleInr σ hmem hrig
  have hinl : doubleInl (k := k) E = tensorInl (k := k) (A := A) (B := E.Carrier) :=
    AlgHom.ext fun _ => rfl
  have hinr : doubleInr (k := k) E = tensorInr (k := k) (A := A) (B := E.Carrier) :=
    AlgHom.ext fun _ => rfl
  rw [hinl, hinr] at hdesc0
  -- the (C2) effectivity theorem for the module-finite cover
  obtain ⟨M, hM⟩ := Over.exists_cechPic_map_whiskerLeft_eq C σ Lc hrig hdesc0
  refine ⟨relPicMk C (overSpec k A) M, ?_⟩
  -- the `mk`-calculus close
  rw [PicEtAff.unit_eq_mk C E (relPicMk C (overSpec k A) M)]
  refine congrArg (PicEtAff.mk C E) (Subtype.ext ?_)
  change relPicAlgMap C ((Algebra.ofId A E.Carrier).restrictScalars k)
      (relPicMk C (overSpec k A) M) = (x : relPic C (overSpec k E.Carrier))
  rw [relPicAlgMap, relPicMap_mk, hM, hLcrep]

end

end AlgebraicGeometry
